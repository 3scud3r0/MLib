#!/usr/bin/env python3
"""Untrusted POSIX-shm proposal client. Models return DSL, never C++ or Lean proofs."""
import argparse
import contextlib
import fcntl
import json
import mmap
import os
from pathlib import Path
import re
import stat
import struct
import subprocess
import time

HEADER = struct.Struct('<8sIIQII')
CAPACITY = 1024 * 1024


@contextlib.contextmanager
def locked(fd, deadline):
    while True:
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            break
        except BlockingIOError:
            if time.monotonic() >= deadline:
                raise TimeoutError('IPC lock timeout')
            time.sleep(.002)
    try:
        yield
    finally:
        fcntl.flock(fd, fcntl.LOCK_UN)


def exchange(name, propose, timeout=60):
    """Read one request, call propose(request_dict), submit DSL, return verdict."""
    if not re.fullmatch(r'/[A-Za-z0-9_-]{1,118}', name):
        raise ValueError('invalid shm name')
    deadline = time.monotonic() + timeout
    path = Path('/dev/shm') / name[1:]
    while True:
        try:
            fd = os.open(path, os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW)
            break
        except FileNotFoundError:
            if time.monotonic() >= deadline:
                raise TimeoutError('mailbox did not appear')
            time.sleep(.002)
    try:
        info = os.fstat(fd)
        if info.st_uid != os.getuid() or info.st_mode & 0o077 or not stat.S_ISREG(info.st_mode):
            raise ValueError('mailbox must be a private file owned by this user')
        # The owner sizes/initializes the mapping immediately after exclusive creation.
        while os.fstat(fd).st_size != HEADER.size + CAPACITY:
            if time.monotonic() >= deadline:
                raise TimeoutError('mailbox initialization timeout')
            time.sleep(.002)
        with mmap.mmap(fd, HEADER.size + CAPACITY) as shared:
            def read():
                magic, version, state, request_id, size, reserved = HEADER.unpack_from(shared)
                if magic != b'GDIPC001' or version != 1 or reserved != 0 or size > CAPACITY:
                    raise ValueError('invalid IPC header')
                return state, request_id, shared[HEADER.size:HEADER.size + size]

            while True:
                with locked(fd, deadline):
                    state, request_id, payload = read()
                    if state == 1:
                        request = json.loads(payload)
                        if request['request_id'] != str(request_id):
                            raise ValueError('request id/header mismatch')
                        break
                if time.monotonic() >= deadline:
                    raise TimeoutError('no request')
                time.sleep(.002)
            replacement = propose(request)
            if not isinstance(replacement, str) or '\n' in replacement or '\r' in replacement:
                raise ValueError('model must return one DSL expression on one line')
            response = (f'GODEL_REPLACE_V1\n{request_id}\n{request["source_blake3"]}\n{replacement}').encode()
            if len(response) >= 100000:
                raise ValueError('proposal exceeds parser budget')
            with locked(fd, deadline):
                state, current_id, _ = read()
                if state != 1 or current_id != request_id:
                    raise ValueError('request changed while model was reasoning')
                shared[HEADER.size:HEADER.size+len(response)] = response
                HEADER.pack_into(shared, 0, b'GDIPC001', 1, 2, request_id, len(response), 0)
            while True:
                with locked(fd, deadline):
                    state, current_id, payload = read()
                    if current_id != request_id:
                        raise ValueError('stale result')
                    if state == 3:
                        return json.loads(payload)
                if time.monotonic() >= deadline:
                    raise TimeoutError('verification result timeout')
                time.sleep(.002)
    finally:
        os.close(fd)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--shm', required=True)
    parser.add_argument('--timeout', type=float, default=60)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--replacement', help='literal DSL proposal for manual tests')
    group.add_argument('--command', nargs=argparse.REMAINDER,
                       help='external model command: JSON request on stdin, DSL on stdout')
    args = parser.parse_args()

    def propose(request):
        if args.replacement is not None:
            return args.replacement
        if not args.command:
            raise ValueError('--command needs an executable')
        result = subprocess.run(args.command, input=json.dumps(request), text=True,
                                capture_output=True, timeout=args.timeout, check=True)
        return result.stdout.strip()

    result = exchange(args.shm, propose, args.timeout)
    print(json.dumps(result, ensure_ascii=False))
    return 0 if result['accepted'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
