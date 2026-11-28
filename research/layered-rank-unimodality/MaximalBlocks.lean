module

public import PeakPolynomial

@[expose] public section

namespace LayeredRanks
open Finset Polynomial
noncomputable section

/-- Insert the separating letter M between successive blocks, keeping both end gaps. -/
def joinBlocks (M : ℕ) (last : List ℕ) : List (List ℕ) → List ℕ
  | [] => last
  | A :: gaps => A ++ M :: joinBlocks M last gaps

theorem joinBlocks_bound (M : ℕ) (last : List ℕ) (gaps : List (List ℕ))
    (bound : ∀ U ∈ gaps ++ [last], ∀ a ∈ U, a ≤ M) :
    ∀ a ∈ joinBlocks M last gaps, a ≤ M := by
  induction gaps with
  | nil => exact bound last (by simp)
  | cons A gaps ih =>
    intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact bound A (by simp) a h
    · rcases List.mem_cons.1 h with rfl | h
      · rfl
      · exact ih (fun U hU => bound U (by simp [hU])) a h

theorem exitPoly_joinBlocks (M : ℕ) (last : List ℕ) (gaps : List (List ℕ))
    (bound : ∀ U ∈ gaps ++ [last], ∀ a ∈ U, a ≤ M) :
    exitPoly M (joinBlocks M last gaps) = ((gaps ++ [last]).map (exitPoly M)).prod := by
  induction gaps with
  | nil => simp [joinBlocks]
  | cons A gaps ih =>
    have rest : ∀ U ∈ gaps ++ [last], ∀ a ∈ U, a ≤ M := fun U hU => bound U (by simp [hU])
    rw [joinBlocks, exitPoly_peak _ _ _ (bound A (by simp)) (joinBlocks_bound _ _ _ rest), ih rest]
    simp

/-- Evaluate the finite expansion by multiplying each block by all preceding exits. -/
def prefixExpansion (M : ℕ) (last : List ℕ) : List (List ℕ) → ℤ[X]
  | [] => rankPoly last
  | A :: gaps => rankPoly A + exitPoly M A * prefixExpansion M last gaps

theorem rankPoly_joinBlocks (M : ℕ) (last : List ℕ) (gaps : List (List ℕ))
    (bound : ∀ U ∈ gaps ++ [last], ∀ a ∈ U, a ≤ M) :
    rankPoly (joinBlocks M last gaps) = prefixExpansion M last gaps := by
  induction gaps with
  | nil => rfl
  | cons A gaps ih =>
    have rest : ∀ U ∈ gaps ++ [last], ∀ a ∈ U, a ≤ M := fun U hU => bound U (by simp [hU])
    rw [joinBlocks, rankPoly_peak _ _ _ (bound A (by simp)) (joinBlocks_bound _ _ _ rest),
      prefixExpansion, ih rest]
    unfold exitPoly
    ring

private theorem exitPoly_injective_rank (M : ℕ) {u v : List ℕ}
    (h : exitPoly M u = exitPoly M v) : rankPoly u = rankPoly v := by
  have hc : (letters 0 M).coeff 0 = 0 := by
    unfold letters
    rw [finsetSum_coeff]
    apply sum_eq_zero
    intro t ht
    have hpos := (Finset.mem_Icc.1 ht).1
    simp [coeff_X_pow, show 0 ≠ t by omega]
  have hne : letters 0 M - 1 ≠ 0 := by
    intro he
    have h0 := congrArg (fun p : ℤ[X] => p.coeff 0) (sub_eq_zero.1 he)
    simp [hc] at h0
  exact mul_left_cancel₀ hne (add_left_cancel h)

/-- Any permutation of all gaps, including moving an end gap, preserves every actual rank. -/
theorem rankCount_perm_blocks (M r : ℕ) (last last' : List ℕ) (gaps gaps' : List (List ℕ))
    (perm : (gaps ++ [last]).Perm (gaps' ++ [last']))
    (bound : ∀ U ∈ gaps ++ [last], ∀ a ∈ U, a ≤ M) :
    rankCount (joinBlocks M last gaps) r = rankCount (joinBlocks M last' gaps') r := by
  have bound' : ∀ U ∈ gaps' ++ [last'], ∀ a ∈ U, a ≤ M :=
    fun U hU => bound U (perm.mem_iff.mpr hU)
  have eq := exitPoly_injective_rank M (u := joinBlocks M last gaps) (v := joinBlocks M last' gaps') (by
    rw [exitPoly_joinBlocks _ _ _ bound, exitPoly_joinBlocks _ _ _ bound']
    exact (perm.map _).prod_eq)
  have coeff := congrArg (fun p : ℤ[X] => p.coeff r) eq
  simpa only [rankPoly_coeff, Int.natCast_inj] using coeff

end
end LayeredRanks
