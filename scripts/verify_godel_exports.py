#!/usr/bin/env python3
"""Replay C++ evidence, check the emitted theorem in Lean, then mark its exact bytes verified."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

from check_proofs import code_only

ROOT = Path(__file__).resolve().parent.parent
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def verify(path, engine):
    source = path.read_bytes()
    tag = re.fullmatch(r'Rewrite_([0-9a-f]{64})\.lean', path.name)
    if not tag:
        raise ValueError('unexpected certificate filename')
    metadata_path = path.with_suffix('.lean.json')
    metadata = json.loads(metadata_path.read_text())
    if metadata['schema'] != 'godel-leanml-rewrite-v2' or metadata['statement_blake3'] != tag[1]:
        raise ValueError('certificate schema or statement mismatch')
    fields = metadata['evidence'].split('|')
    if len(fields) != 7 or fields[0] not in {'ASTv1', 'ASTv2'}:
        raise ValueError('unsupported certificate evidence')
    code = code_only(source.decode())
    if re.search(r'\b(sorry|admit|axiom|native_decide)\b', code):
        raise ValueError('proof hole or new axiom in certificate')
    with tempfile.TemporaryDirectory(prefix='godel-replay-') as tmp:
        # Reconstruct from the evidence, recompute costs and BLAKE3, and require
        # exactly the deterministic translation of those ASTs, not arbitrary Lean.
        subprocess.run([str(engine), '--lean-out', tmp, '--certify', fields[1], fields[2], fields[3]],
                       check=True, capture_output=True, text=True, timeout=60)
        replay = Path(tmp) / path.name
        if not replay.exists() or replay.read_bytes() != source:
            raise ValueError('source is not the canonical translation of the evidence')
        expected = json.loads(replay.with_suffix('.lean.json').read_text())
        if any(metadata[k] != expected[k] for k in ('statement_blake3', 'proof_blake3', 'evidence')):
            raise ValueError('BLAKE3 or evidence mismatch')
        name = f'LeanML.Generated.Cert_{tag[1]}'
        audit = Path(tmp) / 'Audit.lean'
        audit.write_bytes(source + (f'\n#check ({name}.certified : LeanML.Programs.VerifiedRewrite '
                                   f'{name}.before {name}.after)\n#print axioms {name}.certified\n').encode())
        result = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', str(audit)],
                                cwd=ROOT, capture_output=True, text=True, timeout=120)
        if result.returncode:
            raise ValueError(result.stdout + result.stderr)
        audits = re.findall(r'depends on axioms: \[([^]]*)\]', result.stdout)
        if len(audits) != 1 or set(filter(None, map(str.strip, audits[0].split(',')))) - ALLOWED_AXIOMS:
            raise ValueError('unexpected or missing theorem axiom audit')
    metadata.update(lean_status='kernel-verified', lean_source_sha256=hashlib.sha256(source).hexdigest(),
                    lean_toolchain=(ROOT / 'lean-toolchain').read_text().strip())
    # Update status only after successful replay and kernel checking of these bytes.
    with tempfile.NamedTemporaryFile(mode='w', dir=metadata_path.parent, delete=False) as output:
        json.dump(metadata, output, ensure_ascii=False, indent=2)
        output.write('\n')
        temporary = Path(output.name)
    temporary.replace(metadata_path)
    print(f'kernel-verified: {path}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('files', type=Path, nargs='+')
    parser.add_argument('--engine', type=Path, default=ROOT / '.lake/godel/godel')
    args = parser.parse_args()
    for path in args.files:
        try:
            verify(path.resolve(), args.engine.resolve())
        except Exception:
            metadata_path = path.with_suffix('.lean.json')
            if metadata_path.exists():
                metadata = json.loads(metadata_path.read_text())
                metadata['lean_status'] = 'rejected'
                metadata.pop('lean_source_sha256', None)
                with tempfile.NamedTemporaryFile(mode='w', dir=metadata_path.parent, delete=False) as output:
                    json.dump(metadata, output, ensure_ascii=False, indent=2)
                    output.write('\n')
                    temporary = Path(output.name)
                temporary.replace(metadata_path)
            raise


if __name__ == '__main__':
    main()
