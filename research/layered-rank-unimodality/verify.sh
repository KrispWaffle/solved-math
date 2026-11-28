#!/usr/bin/env bash
set -euo pipefail
topic=$(cd "$(dirname "$0")" && pwd)
cd "$topic/../../lean"
if ! command -v lake >/dev/null; then
  export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
fi
lake build Mathlib.Data.List.Forall2 Mathlib.Order.Interval.Finset.Nat \
  Mathlib.Algebra.BigOperators.Intervals Mathlib.Algebra.Order.BigOperators.Group.Finset \
  Mathlib.Tactic.Ring Mathlib.Tactic.Tauto
objects=$(mktemp -d)
trap 'rm -rf -- "$objects"' EXIT
lake env bash -eu -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  for module in GreedyBoxes BoxProfiles; do
    lean -DwarningAsError=true --root="$2" -o "$1/$module.olean" "$2/$module.lean"
    leanchecker --fresh --verbose "$module"
  done
  lean -DwarningAsError=true "$2/ProofAudit.lean"
' _ "$objects" "$topic"
python3 "$topic/check.py"
