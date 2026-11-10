#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/activate.sh
python3 scripts/check_proofs.py
lake --wfail build
lake env lean -DwarningAsError=true LeanMLTest/Basic.lean
lake env lean -DwarningAsError=true LeanMLTest/Advanced.lean
lake env lean -DwarningAsError=true LeanMLTest/Axioms.lean > .lake/leanml-axioms.log
if rg -q 'sorryAx|Lean.ofReduceBool|Lean.trustCompiler' .lake/leanml-axioms.log; then
  cat .lake/leanml-axioms.log
  exit 1
fi
cat .lake/leanml-axioms.log
