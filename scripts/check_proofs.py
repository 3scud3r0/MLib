#!/usr/bin/env python3
"""Reject proof holes and new axioms in active Lean sources, preserving nested comments."""
from pathlib import Path
import re
import sys


def code_only(source):
    output = []
    depth, string, escaped = 0, False, False
    i = 0
    while i < len(source):
        pair = source[i:i+2]
        c = source[i]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
            else:
                output.append('\n' if c == '\n' else ' ')
                i += 1
        elif string:
            output.append('\n' if c == '\n' else ' ')
            if escaped:
                escaped = False
            elif c == '\\':
                escaped = True
            elif c == '"':
                string = False
            i += 1
        elif pair == '/-':
            depth = 1
            output.append('  ')
            i += 2
        elif pair == '--':
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        elif c == '"':
            string = True
            output.append(' ')
            i += 1
        else:
            output.append(c)
            i += 1
    if depth or string:
        raise ValueError('Unterminated Lean comment or string')
    return ''.join(output)


def main():
    root = Path(__file__).resolve().parent.parent
    files = [root/'LeanML.lean', *sorted((root/'LeanML').rglob('*.lean')),
             *sorted((root/'LeanMLTest').rglob('*.lean'))]
    violations = []
    for path in files:
        code = code_only(path.read_text())
        for match in re.finditer(r'\b(sorry|admit|axiom|native_decide)\b', code):
            line = code[:match.start()].count('\n')+1
            violations.append(f'{path.relative_to(root)}:{line}: {match.group()}')
    if violations:
        print('\n'.join(violations), file=sys.stderr)
        return 1
    print(f'Proof-source check: {len(files)} active Lean files, no holes or new axioms.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
