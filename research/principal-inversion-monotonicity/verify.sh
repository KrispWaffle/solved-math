#!/usr/bin/env bash
set -euo pipefail
topic=$(cd "$(dirname "$0")" && pwd)
cd "$topic/../../lean"
if ! command -v lake >/dev/null; then
  export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
fi
lake build SolvedMath.HigherInversionComponents Mathlib.Data.Nat.Sqrt Mathlib.Data.Finset.Prod
objects=$(mktemp -d)
trap 'rm -rf -- "$objects"' EXIT
lake env bash -eu -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  lean -DwarningAsError=true --root="$2" -o "$1/UpperEdge.olean" "$2/UpperEdge.lean"
  leanchecker --fresh --verbose UpperEdge
  lean -DwarningAsError=true "$2/ProofAudit.lean"
' _ "$objects" "$topic"
