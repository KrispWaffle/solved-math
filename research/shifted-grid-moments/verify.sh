#!/usr/bin/env bash
set -euo pipefail

topic=$(cd "$(dirname "$0")" && pwd)
cd "$topic/../../lean"
if ! command -v lake >/dev/null && [[ -x "${ELAN_HOME:-$HOME/.elan}/bin/lake" ]]; then
  export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
fi

mapfile -t imports < <(sed -n 's/^import //p' "$topic/FixedMinors.lean")
for module in "${imports[@]}"; do
  if [[ ! -f ".lake/packages/mathlib/.lake/build/lib/lean/${module//./\/}.olean" ]]; then
    lake exe cache get "${imports[@]}"
    break
  fi
done

build=$(mktemp -d)
trap 'rm -rf -- "$build"' EXIT
lake env lean -DwarningAsError=true -R "$topic" -o "$build/FixedMinors.olean" "$topic/FixedMinors.lean"
lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; leanchecker --fresh FixedMinors' _ "$build"
python3 "$topic/check.py"
