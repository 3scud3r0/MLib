#!/usr/bin/env bash
set -euo pipefail
cd /workspace/MLib
python -m venv .venv
.venv/bin/python -m pip install -e .
.venv/bin/python ml_mathlib.py --test-all
.venv/bin/python replay_certificate.py examples/central_force_conservation.json
