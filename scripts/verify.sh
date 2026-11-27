#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
(
  cd lean
  lake build
  lake env leanchecker --fresh --verbose SolvedMath
)
python3 -m unittest discover -s tests
for verifier in results/*/verify.py; do
  python3 "$verifier"
done
