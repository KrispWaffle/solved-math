#!/usr/bin/env bash
set -euo pipefail

if ! command -v lake >/dev/null && [[ -x "${ELAN_HOME:-$HOME/.elan}/bin/lake" ]]; then
  export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
fi

cd "$(dirname "$0")/.."
(
  cd lean
  lake build
  lake env leanchecker --fresh --verbose SolvedMath
)
python3 -m unittest discover -s tests
shopt -s nullglob
for verifier in results/*/verify.py archive/*/verify.py; do
  python3 "$verifier"
done
