#!/usr/bin/env bash
set -euo pipefail
topic=$(cd "$(dirname "$0")" && pwd)
cd "$topic/../../lean"
if ! command -v lake >/dev/null; then
  export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
fi
lake build SolvedMath.RandomPatternDisplacements
objects=$(mktemp -d)
trap 'rm -rf -- "$objects"' EXIT
lake env bash -eu -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  for module in SliceCurvature RankTransfer; do
    lean -DwarningAsError=true --root="$2" -o "$1/$module.olean" "$2/$module.lean"
  done
  leanchecker --fresh --verbose SliceCurvature RankTransfer
' _ "$objects" "$topic"
python3 "$topic/check.py"
