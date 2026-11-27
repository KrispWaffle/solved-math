#!/usr/bin/env bash
set -euo pipefail

if ! command -v lake >/dev/null && [[ -x "${ELAN_HOME:-$HOME/.elan}/bin/lake" ]]; then
  export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
fi

cd "$(dirname "$0")/.."
(
  cd lean
  if [[ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.olean ]]; then
    lake exe cache get Mathlib.Analysis.SpecialFunctions.Pow.Real Mathlib.Data.Fintype.Card \
      Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic Mathlib.Logic.Equiv.Fin.Basic \
      Mathlib.Probability.Moments.SubGaussian Mathlib.Data.Fin.Tuple.Sort \
      Mathlib.MeasureTheory.Constructions.UnitInterval Mathlib.Tactic.FieldSimp \
      Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Tactic.Ring
  fi
  lake build
  lake env leanchecker --fresh --verbose SolvedMath
)
python3 -m unittest discover -s tests
shopt -s nullglob
for verifier in results/*/verify.py archive/*/verify.py; do
  python3 "$verifier"
done
