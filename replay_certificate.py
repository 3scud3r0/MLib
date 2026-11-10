#!/usr/bin/env python3
"""Replay exact conservation certificates in Python (NOT Lean kernel proof)."""
from pathlib import Path
from argparse import ArgumentParser
from ml_mathlib_exact import verify_conservation_certificate

def main():
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('file',type=Path)
    args=parser.parse_args()
    if args.file.stat().st_size>10_000_000:
        raise SystemExit('ERROR: Proof exceeds 10 MB')
    correct=verify_conservation_certificate(args.file.read_text(encoding='utf-8'))
    print('OK: Exact Poisson identity replayed' if correct else 'FAIL: Invalid certificate')
    return 0 if correct else 1

if __name__=='__main__':
    raise SystemExit(main())
