module

public import SolvedMath.ClusterSpineBounds

/-! Comparing the empirical grid, the marked grid and the quantile used by Lee and Sah. -/
@[expose] public section
namespace LeeSah
open MeasureTheory Filter Set
open scoped Topology unitInterval
noncomputable section

private lemma grid_shift {n i : ℝ} (hn : 0 < n) (hi : 0 ≤ i) (hin : i ≤ n) :
    |i/n-(i+1)/(n+2)| ≤ 1/n := by
  rw [show i/n-(i+1)/(n+2) = (2*i-n)/(n*(n+2)) by field_simp; ring,
    abs_div,abs_of_pos (mul_pos hn (by linarith)), div_le_div_iff₀ (mul_pos hn (by linarith)) hn]
  have h : |2*i-n| ≤ n := abs_le.mpr ⟨by linarith,by linarith⟩
  nlinarith [mul_le_mul_of_nonneg_right h hn.le]

private lemma reference_good_all (p q c N : ℕ) (hN : 0 < N) (ξ : ℝ)
    (z : Fin (N+1) → I) (hz : StrictMono z) (good : z ∉ referenceBad p q c N ξ) (k : Fin (N+1)) :
    |betaCdf p q c (z k)-(k.val:ℝ)/N| ≤ ξ+1/N := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have obs (j : Fin N) : |betaCdf p q c (z j.succ)-((j.val:ℝ)+1)/N| ≤ ξ :=
    le_of_not_gt fun h => good ⟨j,h⟩
  refine Fin.cases ?_ (fun j => ?_) k
  · let first : Fin N := ⟨0,hN⟩
    have low : 0 ≤ betaCdf p q c (z 0) := (betaMap p q c (z 0)).property.1
    have hz₁ := (betaCdf_strict p q c).monotoneOn (z 0).property (z first.succ).property
      (show (z 0:ℝ) ≤ z first.succ from hz.monotone (Fin.zero_le first.succ))
    have high := (abs_le.mp (obs first)).2
    simp only [first, Nat.cast_zero,zero_add] at high
    simpa only [Fin.val_zero,Nat.cast_zero,zero_div,sub_zero,abs_of_nonneg low] using
      (show betaCdf p q c (z 0) ≤ ξ+1/N by linarith)
  · simpa only [Fin.val_succ,Nat.cast_add,Nat.cast_one] using
      (obs j).trans (le_add_of_nonneg_right (one_div_nonneg.mpr hn.le))

/-- For a fixed tolerance in label space, a sufficiently fine grid transfers
every bad marked label to a bad coordinate of the reference sample. -/
theorem labelBad_implies_reference (p q c : ℕ) (hc : 0 < c) (η : ℝ) (hη : 0 < η) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ᶠ n : ℕ in atTop, cone (n*c+1) ∩ {z : Spine c n | labelBad p q c η z}
      ⊆ cone (n*c+1) ∩ referenceBad p q c (n*c) ξ := by
  obtain ⟨δ,hδ,close⟩ := Metric.uniformContinuous_iff.mp (uniformContinuous_quantile p q c) η hη
  let ξ := δ/4
  have hξ : 0 < ξ := by dsimp [ξ]; linarith
  refine ⟨ξ,hξ,?_⟩
  have fine : ∀ᶠ n : ℕ in atTop, (1:ℝ)/n < ξ := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const hξ
  filter_upwards [fine,eventually_ge_atTop 1] with n hf hn
  rintro z ⟨hz,⟨i,bad⟩⟩
  refine ⟨hz,?_⟩
  by_contra good
  have npos : (0:ℝ) < n := by exact_mod_cast hn
  have cpos : (0:ℝ) < c := by exact_mod_cast hc
  have hN : 0 < n*c := Nat.mul_pos hn hc
  have nc : (n:ℝ) ≤ n*c := by
    have cp : (1:ℝ) ≤ c := by exact_mod_cast hc
    simpa using mul_le_mul_of_nonneg_left cp npos.le
  have inum : (i.val:ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  let u : I := ⟨((i.val:ℝ)+1)/((n:ℝ)+2), by
    refine ⟨by positivity,(div_le_one (by linarith)).mpr (by linarith)⟩⟩
  let v := betaMap p q c (z (mark c i))
  have obs := reference_good_all p q c (n*c) hN ξ z hz good (mark c i)
  have rat : ((mark c i).val:ℝ)/(n*c:ℕ) = (i.val:ℝ)/n := by
    simp only [mark,Nat.cast_mul]
    exact mul_div_mul_right _ _ cpos.ne'
  rw [rat,Nat.cast_mul] at obs
  have mesh := one_div_le_one_div_of_le npos nc
  have shift := grid_shift npos (show 0 ≤ (i.val:ℝ) by positivity) inum
  have dist₁ : dist v u < δ := by
    rw [Subtype.dist_eq,Real.dist_eq]
    change |betaCdf p q c (z (mark c i))-((i.val:ℝ)+1)/((n:ℝ)+2)| < δ
    have tri := abs_sub_le (betaCdf p q c (z (mark c i))) ((i.val:ℝ)/n) (((i.val:ℝ)+1)/((n:ℝ)+2))
    dsimp [ξ] at hf obs
    linarith
  have H := close dist₁
  have inv : betaQuantile p q c v = (z (mark c i):ℝ) :=
    (betaQuantile_eq_inverse p q c v).trans (congrArg Subtype.val ((betaIso p q c).symm_apply_apply _))
  rw [Real.dist_eq,inv] at H
  exact (not_lt_of_ge (le_of_lt H)) bad

end
end LeeSah
