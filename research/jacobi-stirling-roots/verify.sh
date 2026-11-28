#!/usr/bin/env bash
set -euo pipefail

topic=$(cd "$(dirname "$0")" && pwd)
cd "$topic/../../lean"
if ! command -v lake >/dev/null; then
  export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
fi
mapfile -t deps < <(sed -n 's/^import //p' "$topic"/*.lean | sort -u)
for dep in "${deps[@]}"; do
  if [[ ! -f ".lake/packages/mathlib/.lake/build/lib/lean/${dep//./\/}.olean" ]]; then
    lake exe cache get "${deps[@]}"
    break
  fi
done

objects=$(mktemp -d)
trap 'rm -rf -- "$objects"' EXIT
for module in Reduction ExtremeRoots; do
  lake env lean -DwarningAsError=true --root="$topic" -o "$objects/$module.olean" "$topic/$module.lean"
  lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec leanchecker --fresh --verbose "$2"' _ "$objects" "$module"
done
python3 "$topic/check.py"
python3 "$topic/check_extremes.py"
