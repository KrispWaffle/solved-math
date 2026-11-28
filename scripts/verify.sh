#!/usr/bin/env bash
set -euo pipefail

if ! command -v lake >/dev/null && [[ -x "${ELAN_HOME:-$HOME/.elan}/bin/lake" ]]; then
  export PATH="${ELAN_HOME:-$HOME/.elan}/bin:$PATH"
fi

cd "$(dirname "$0")/.."
(
  cd lean
  if [[ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Analysis/SpecialFunctions/Exponential.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/MeasureTheory/Integral/Pi.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Probability/Moments/SubGaussian.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/LinearAlgebra/Charpoly/Basic.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Fin/VecNotation.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic/FinCases.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Logic/Equiv/Set.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/Finset/BooleanAlgebra.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Combinatorics/Derangements/Basic.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Order/Circular/ZMod.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Order/Interval/Finset/Fin.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Analysis/SpecificLimits/Normed.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Algebra/Order/Floor/Ring.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/List/Permutation.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Data/List/Sublists.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/SetTheory/Cardinal/Finite.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Combinatorics/SimpleGraph/Maps.olean ||
        ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Computability/TuringMachine/PostTuringMachine.olean ]]; then
    lake exe cache get Mathlib.Analysis.SpecialFunctions.Pow.Real Mathlib.Data.Fintype.Card \
      Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic Mathlib.Logic.Equiv.Fin.Basic \
      Mathlib.MeasureTheory.Integral.Prod Mathlib.MeasureTheory.Integral.Pi \
      Mathlib.MeasureTheory.Integral.DominatedConvergence Mathlib.Order.Preorder.Finite \
      Mathlib.Analysis.SpecialFunctions.Pow.Continuity Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics \
      Mathlib.Topology.Order.IntermediateValue Mathlib.Order.Fin.Tuple \
      Mathlib.Probability.Moments.SubGaussian Mathlib.Data.Fin.Tuple.Sort \
      Mathlib.MeasureTheory.Constructions.UnitInterval Mathlib.Tactic.FieldSimp \
      Mathlib.Tactic.Linarith Mathlib.Tactic.Positivity Mathlib.Tactic.Ring \
      Mathlib.LinearAlgebra.Charpoly.Basic Mathlib.Algebra.LinearRecurrence \
      Mathlib.Data.Int.Interval Mathlib.Analysis.Complex.Basic Mathlib.Data.List.OfFn \
      Mathlib.Data.Fintype.Perm Mathlib.Algebra.BigOperators.Fin \
      Mathlib.Data.Finset.Sort Mathlib.Data.Finset.Powerset Mathlib.Algebra.BigOperators.Field \
      Mathlib.Analysis.SpecialFunctions.Exponential Mathlib.Logic.Equiv.Set \
      Mathlib.Data.Finset.BooleanAlgebra Mathlib.Tactic.FinCases Mathlib.Data.Fin.VecNotation \
      Mathlib.Combinatorics.Derangements.Basic Mathlib.Order.Circular.ZMod Mathlib.Analysis.SpecificLimits.Basic \
      Mathlib.Order.Interval.Finset.Fin Mathlib.Data.Fin.Rev \
      Mathlib.Analysis.SpecificLimits.Normed Mathlib.Algebra.Order.Floor.Ring \
      Mathlib.Data.List.Permutation Mathlib.Data.List.Sublists Mathlib.SetTheory.Cardinal.Finite \
      Mathlib.Combinatorics.SimpleGraph.Maps Mathlib.Computability.TuringMachine.PostTuringMachine \
      Mathlib.Data.Fintype.BigOperators Mathlib.Algebra.Order.BigOperators.Group.Finset
  fi
  lake build
  lake env leanchecker --fresh --verbose SolvedMath
)
python3 -m unittest discover -s tests
shopt -s nullglob
for verifier in results/*/verify.py archive/*/verify.py; do
  python3 "$verifier"
done
