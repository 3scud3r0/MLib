#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/activate.sh
mkdir -p .lake/godel
compiler="${CXX:-g++}"
"$compiler" -std=c++17 -O2 -Wall -Wextra -Werror tools/godel/godel.cpp \
  -lgmpxx -lgmp -ldl -o .lake/godel/godel
.lake/godel/godel --self-test
"$compiler" -std=c++17 -O1 -g -Wall -Wextra -Werror \
  -fsanitize=address,undefined -fno-omit-frame-pointer tests/godel/unit.cpp \
  -lgmpxx -lgmp -ldl -o .lake/godel/unit
.lake/godel/unit
lake --wfail build
python3 tests/godel/integration.py .lake/godel/godel
if compgen -G 'examples/godel/Rewrite_*.lean' > /dev/null; then
  python3 scripts/verify_godel_exports.py examples/godel/Rewrite_*.lean
fi
