#!/usr/bin/env bash
set -euo pipefail

topic=$(cd "$(dirname "$0")" && pwd)
cd "$topic/../../lean"
if ! command -v lake >/dev/null; then
  export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
fi
mapfile -t deps < <(sed -n 's/^import \(Mathlib\..*\)$/\1/p' "$topic"/*.lean | sort -u)
for dep in "${deps[@]}"; do
  if [[ ! -f ".lake/packages/mathlib/.lake/build/lib/lean/${dep//./\/}.olean" ]]; then
    lake exe cache get "${deps[@]}"
    break
  fi
done

objects=$(mktemp -d)
trap 'rm -rf -- "$objects"' EXIT
lake env bash -eu -c '
  export LEAN_PATH="$1:$LEAN_PATH"
  for module in Reduction ExtremeRoots SourcePolynomial Reciprocal; do
    lean -DwarningAsError=true --root="$2" -o "$1/$module.olean" "$2/$module.lean"
    leanchecker --fresh --verbose "$module"
  done
' _ "$objects" "$topic"
python3 "$topic/check.py"
python3 "$topic/check_extremes.py"
python3 "$topic/check_reciprocal.py"
