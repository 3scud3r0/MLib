#!/usr/bin/env python3
"""End-to-end tests: exact proposals -> shared memory -> generated Lean -> kernel."""
import fcntl
import importlib.util
import json
import mmap
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import uuid

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('godel_propose', ROOT/'tools/godel/propose.py')
client = importlib.util.module_from_spec(spec)
spec.loader.exec_module(client)
ENGINE = Path(sys.argv[1]).resolve()


def run(args, *, success=True):
    result = subprocess.run([str(ENGINE), *args], capture_output=True, text=True, timeout=30)
    assert (result.returncode == 0) == success, str(args)+"\n"+result.stdout + result.stderr
    return result


def ipc(directory, replacement=None, corrupt=None, timeout=5000, external=False):
    name = '/godel_test_' + uuid.uuid4().hex
    server = subprocess.Popen([str(ENGINE), '--lean-out', str(directory), '--ipc-optimize',
                               name, '1', '(x0+0)', str(timeout)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    try:
        if corrupt:
            path = Path('/dev/shm') / name[1:]
            deadline = time.monotonic() + 5
            while not path.exists() or path.stat().st_size != client.HEADER.size + client.CAPACITY:
                assert time.monotonic() < deadline
                time.sleep(.002)
            with path.open('r+b') as f, mmap.mmap(f.fileno(), 0) as shared:
                while True:
                    with client.locked(f.fileno(), deadline):
                        header = client.HEADER.unpack_from(shared)
                        if header[2] == 1:
                            request = json.loads(shared[client.HEADER.size:client.HEADER.size+header[4]])
                            break
                    time.sleep(.002)
                response = f'GODEL_REPLACE_V1\n{request["request_id"]}\n{request["source_blake3"]}\nx0'
                if corrupt == 'stale':
                    response = response.replace(request['request_id'], '0')
                if corrupt == 'hash':
                    response = response.replace(request['source_blake3'], '0'*64)
                payload = response.encode()
                with client.locked(f.fileno(), deadline):
                    shared[client.HEADER.size:client.HEADER.size+len(payload)] = payload
                    size = client.CAPACITY+1 if corrupt == 'oversize' else len(payload)
                    client.HEADER.pack_into(shared, 0, b'GDIPC001', 1, 2, header[3], size, 0)
            verdict = None
        elif external:
            result = subprocess.run([sys.executable, 'tools/godel/propose.py', '--shm', name,
                '--command', sys.executable, '-c',
                'import json,sys; request=json.load(sys.stdin); assert request["variables"]==1; print("x0")'],
                cwd=ROOT, capture_output=True, text=True, timeout=10)
            assert result.returncode == 0, result.stdout+result.stderr
            verdict = json.loads(result.stdout)
        elif replacement is not None:
            verdict = client.exchange(name, lambda _: replacement, 10)
        else:
            verdict = None
        stdout, stderr = server.communicate(timeout=10)
        expected = (replacement == 'x0' or external) and corrupt is None
        assert (server.returncode == 0) == expected, stdout+stderr
        if verdict is not None:
            assert verdict['accepted'] == expected
            if expected:
                assert verdict['lean_status'] == 'pending-kernel'
        assert not (Path('/dev/shm')/name[1:]).exists(), 'mailbox leaked'
        return verdict
    finally:
        if server.poll() is None:
            server.kill()
            server.wait()


with tempfile.TemporaryDirectory(prefix='leanml-godel-') as tmp:
    output = Path(tmp)
    positive = [
        (1, '(x0+0)', 'x0'),
        (1, 'q(-1/2)+x0+0', 'x0+q(-1/2)'),
        (1, 'fold(3,x0,iflt(i0,1,a0+1,a0+2))', 'x0+5'),
        (1, 'fold(3,x0,a0+i0)', '(x0+3)'),
        (1, 'fold(0,x0,a0+999)', 'x0'),
        (1, 'iflt(x0,0,x0+0,x0)', 'x0'),
        (2, 'iflt(x0,0,x0*(x1+1)+0,x0+x1+0)', 'iflt(x0,0,x0*x1+x0,x1+x0)'),
        (1, 'fold(2,x0,fold(3,a0,a0+i0+i1))', '(x0+9)'),
        (2, 'fold(2,tensor([2],[x0,x1]),a0+tensor([2],[1,i0]))', 'tensor([2],[x0+2,x1+1])'),
        (2, 'matmul(tensor([1,2],[x0,x1]),tensor([2,1],[1,2]))', 'tensor([1,1],[x0+2*x1])'),
        (1, 'iflt(x0,0,tensor([2],[x0+0,1]),tensor([2],[x0,1]))', 'tensor([2],[x0,1])'),
    ]
    for n, before, after in positive:
        run(['--lean-out', str(output), '--certify', str(n), before, after])
    for before, after in [('x0', 'x0+1'), ('x0', 'x0'), ('iflt(x0,999999,x0,0)', 'x0'),
                          ('fold(3,x0,a0+i0)', 'x0+6')]:
        run(['--lean-out', str(output), '--certify', '1', before, after], success=False)
    run(['--lean-out', str(output), '--optimize', '1', 'iflt(x0,0,x0+0,x0+0)', '40'])
    run(['--knowledge', str(output/'memory.bt'), '--lean-out', str(output), '--evolve', '40'])
    files = sorted(output.glob('*.lean'))
    assert len(files) >= len(positive)
    subprocess.run([sys.executable, 'scripts/verify_godel_exports.py', '--engine', str(ENGINE),
                    *map(str, files)], cwd=ROOT, check=True, timeout=180)
    for f in files:
        assert json.loads(f.with_suffix('.lean.json').read_text())['lean_status'] == 'kernel-verified'
    # Tampering with the generated statement cannot inherit a verified status.
    victim = files[0]
    original = victim.read_bytes()
    victim.write_bytes(original.replace(b'theorem certified', b'theorem forged'))
    tampered = subprocess.run([sys.executable, 'scripts/verify_godel_exports.py', '--engine', str(ENGINE), str(victim)],
                              cwd=ROOT, capture_output=True, timeout=30)
    assert tampered.returncode != 0
    assert json.loads(victim.with_suffix('.lean.json').read_text())['lean_status'] == 'rejected'
    victim.write_bytes(original)
    ipc(output, replacement='x0')
    verdict = ipc(output/'external', external=True)
    subprocess.run([sys.executable, 'scripts/verify_godel_exports.py', '--engine', str(ENGINE),
                    verdict['lean_file']], cwd=ROOT, check=True, timeout=60)
    for name, kwargs in [('false', {'replacement':'x0+1'}), ('syntax', {'replacement':'a0'}),
                         ('stale', {'corrupt':'stale'}), ('hash', {'corrupt':'hash'}),
                         ('oversize', {'corrupt':'oversize'}), ('timeout', {'timeout':30})]:
        folder = output/name
        ipc(folder, **kwargs)
        assert not folder.exists(), f'rejected proposal exported a proof: {name}'
print('Godel integration: 11 exact rewrites, GNN, Lean replay/audits, tampering, 8 IPC cases passed')
