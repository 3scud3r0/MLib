#!/usr/bin/env python3
"""Run a bounded untrusted-proposer -> trusted-Rust-verifier demonstration.

Prerequisites:
    cd mlib-core && maturin develop --features python
    python examples/nabla_verified_discovery.py

Optional NVIDIA/CPU model checkpoint (trusted torch weight format only):
    PYTHONPATH=. python examples/nabla_verified_discovery.py \
        --checkpoint /path/to/ckpt.pt --samples 8 --device cpu
    # `nabla_gpt_cuda.py` must be importable for the checkpoint example.
"""
from __future__ import annotations
import argparse
import json

from mlib_core import Kernel, PhaseSpace, DiscoverySession, NablaCheckpointSampler


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkpoint", help="Trusted NABLA-GPT weight checkpoint")
    parser.add_argument("--samples", type=int, default=5)
    parser.add_argument("--device", default="cpu", help="cpu/cuda")
    parser.add_argument("--seed", type=int, default=1)
    args = parser.parse_args()
    if not 1 <= args.samples <= 32:
        parser.error("--samples deve estar em 1..32")

    phase = PhaseSpace(1)
    q, p = phase.coordinates()
    hamiltonian = p**2 / 2 + q**4 / 4
    session = DiscoverySession(Kernel(), phase, hamiltonian)

    if args.checkpoint:
        sampler = NablaCheckpointSampler.from_checkpoint(args.checkpoint, device=args.device, seed=args.seed)
        results = session.run_sampler(sampler, prompt="Q = ", count=args.samples)
    else:
        proposals = [
            "Q = q0",                     # False: {q,H}=p
            "Q = p0**2/2 + q0**4/4",      # True: energy
            "Q = __import__('os')",       # Malicious code, parse rejection
            "Q = p0",                     # False: {p,H}=-q**3
            "Q = q0**2 + p0**2",          # False: not quartic energy
        ]
        results = session.verify(proposals, limit=args.samples)

    for report in results:
        print(json.dumps({
            "candidate": report.text,
            "accepted": report.accepted,
            "digest": report.digest,
            "claim": report.theorem.claim if report.theorem else None,
            "domain_exclusions": report.theorem.original_domain_exclusions if report.theorem else [],
            "error": report.error,
        }, ensure_ascii=False))


if __name__ == "__main__":
    main()
