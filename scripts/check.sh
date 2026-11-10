#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/activate.sh
python3 scripts/verify_legacy.py --sources-only
python3 scripts/check_proofs.py
lake build
lake env lean LeanMLTest/Basic.lean
lake env lean LeanMLTest/Axioms.lean > .lake/leanml-axioms.log
if rg -q 'sorryAx|Lean.ofReduceBool|Lean.trustCompiler' .lake/leanml-axioms.log; then
  cat .lake/leanml-axioms.log
  exit 1
fi
cat .lake/leanml-axioms.log
