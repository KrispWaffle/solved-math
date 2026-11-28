module

public import SolvedMath.DerangementEndpoints
public import Mathlib.Data.Fin.Rev

@[expose] public section

namespace DerangementSpectrum

open Finset
noncomputable section

/-- Actual local positions whose global position agrees with their global value. -/
def fixedInBlock {h : ℕ} (u v : ℕ) (π : Perm h) : Finset (Fin h) :=
  univ.filter (fun j => u + j.val = v + (π j).val)

theorem increasing_block_count (u v h : ℕ) :
    (fixedInBlock u v (Equiv.refl (Fin h))).card = if u = v then h else 0 := by
  classical
  by_cases huv : u = v <;> simp [fixedInBlock, huv]

/-- For a decreasing block the equation for a fixed point is twice its local coordinate. -/
theorem decreasing_block_equation {h : ℕ} (u v : ℕ) (j : Fin h) :
    j ∈ fixedInBlock u v Fin.revPerm ↔
      2 * (j.val : ℤ) = (v : ℤ) - u + h - 1 := by
  simp only [fixedInBlock, mem_filter, mem_univ, true_and]
  change u + j.val = v + (h - (j.val+1)) ↔ _
  have hj := j.isLt
  omega

theorem decreasing_block_count (u v h : ℕ) :
    (fixedInBlock u v (@Fin.revPerm h)).card =
      if -(h-1 : ℤ) ≤ (v:ℤ)-u ∧ (v:ℤ)-u ≤ h-1 ∧ ((v:ℤ)-u+h-1) % 2 = 0
        then 1 else 0 := by
  classical
  let S := fixedInBlock u v (@Fin.revPerm h)
  have single : S.card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    have ea := (decreasing_block_equation u v a).mp ha
    have eb := (decreasing_block_equation u v b).mp hb
    apply Fin.ext
    omega
  have hit : S.Nonempty ↔ -(h-1 : ℤ) ≤ (v:ℤ)-u ∧ (v:ℤ)-u ≤ h-1 ∧
      ((v:ℤ)-u+h-1) % 2 = 0 := by
    constructor
    · rintro ⟨j, hj⟩
      have e := (decreasing_block_equation u v j).mp hj
      have hj' := j.isLt
      omega
    · rintro ⟨hl, hr, he⟩
      let q : ℤ := ((v:ℤ)-u+h-1) / 2
      have hq : 0 ≤ q := by dsimp [q]; omega
      have hbound : q.toNat < h := by dsimp [q]; omega
      refine ⟨⟨q.toNat, hbound⟩, (decreasing_block_equation _ _ _).2 ?_⟩
      change 2 * (q.toNat : ℤ) = _
      rw [Int.toNat_of_nonneg hq]
      dsimp [q]
      omega
  change S.card = _
  split_ifs with hhit
  · have hp := Finset.card_pos.mpr (hit.mpr hhit)
    omega
  · exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp (fun h => hhit (hit.mp h)))

end
end DerangementSpectrum
