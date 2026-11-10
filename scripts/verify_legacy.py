#!/usr/bin/env python3
"""Verify preservation of the pre-migration files retained in the local archive.
Generated files may be absent in a fresh Git clone because they are ignored.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sources-only', action='store_true', help='Allow omitted archived generated artifacts')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent/'legacy'
    manifest = json.loads((root/'ARCHIVE_MANIFEST.json').read_text())
    generated = {'.venv', '__pycache__', 'build', 'ml_mathlib.egg-info', '.lake'}
    checked = 0
    for name, expected in manifest['files'].items():
        path = root/name
        if args.sources_only and Path(name).parts[0] in generated:
            continue
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit(f'Archive content differs: {name}')
        checked += 1
    for name, expected in manifest['symlinks'].items():
        if args.sources_only and Path(name).parts[0] in generated:
            continue
        if os.readlink(root/name) != expected:
            raise SystemExit(f'Archive symlink differs: {name}')
    print(f'Archive verified: {checked} files; original source content preserved.')
    upstream = root/'UPSTREAM_ARCHIVE_MANIFEST.json'
    if upstream.exists():
        additional = json.loads(upstream.read_text())
        for name, expected in additional['files'].items():
            if hashlib.sha256((root/name).read_bytes()).hexdigest() != expected:
                raise SystemExit(f'Upstream archive content differs: {name}')
        print(f'Upstream archive verified: {len(additional["files"])} additional files.')


if __name__ == '__main__':
    main()
