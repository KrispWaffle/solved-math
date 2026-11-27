module

public import SolvedMath.ClusterHeight
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-! The beta distribution function and its inverse in the original height conjecture. -/
@[expose] public section
namespace LeeSah
open MeasureTheory Set Function Filter
open scoped unitInterval Topology
noncomputable section

lemma continuous_betaWeight (p q c : ℕ) : Continuous (betaWeight p q c) := by
  exact (continuous_id.rpow_const (fun _ => Or.inr (by positivity))).mul
    ((continuous_const.sub continuous_id).rpow_const (fun _ => Or.inr (by positivity)))

lemma betaWeight_nonneg (p q c : ℕ) {x : ℝ} (hx : x ∈ Icc 0 1) : 0 ≤ betaWeight p q c x :=
  mul_nonneg (Real.rpow_nonneg hx.1 _) (Real.rpow_nonneg (sub_nonneg.mpr hx.2) _)

lemma betaWeight_positive (p q c : ℕ) {x : ℝ} (hx : x ∈ Ioo 0 1) : 0 < betaWeight p q c x :=
  mul_pos (Real.rpow_pos_of_pos hx.1 _) (Real.rpow_pos_of_pos (sub_pos.mpr hx.2) _)

lemma betaWeight_le_one (p q c : ℕ) {x : ℝ} (hx : x ∈ Icc 0 1) : betaWeight p q c x ≤ 1 := by
  have a := Real.rpow_le_rpow hx.1 hx.2 (show 0 ≤ (p:ℝ)/c by positivity)
  have b := Real.rpow_le_rpow (sub_nonneg.mpr hx.2) (show 1-x ≤ 1 by linarith [hx.1])
    (show 0 ≤ (q:ℝ)/c by positivity)
  simpa [betaWeight] using mul_le_mul a b (Real.rpow_nonneg (sub_nonneg.mpr hx.2) _) (by simp)

lemma beta_segment_positive (p q c : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ 1) (hxy : x < y) :
    0 < ∫ t in x..y, betaWeight p q c t := by
  apply intervalIntegral.integral_pos hxy (continuous_betaWeight p q c).continuousOn
  · intro t ht; exact betaWeight_nonneg p q c ⟨hx.trans ht.1.le, ht.2.trans hy⟩
  · refine ⟨(x+y)/2, ⟨by linarith,by linarith⟩, betaWeight_positive p q c ⟨by linarith,by linarith⟩⟩

lemma beta_mass_pos (p q c : ℕ) : 0 < ∫ t in (0:ℝ)..1, betaWeight p q c t :=
  beta_segment_positive p q c le_rfl le_rfl zero_lt_one

lemma continuous_betaCdf (p q c : ℕ) : Continuous (betaCdf p q c) :=
  (intervalIntegral.continuous_primitive (fun _ _ => (continuous_betaWeight p q c).intervalIntegrable ..) 0).div_const _

lemma betaCdf_strict (p q c : ℕ) : StrictMonoOn (betaCdf p q c) (Icc 0 1) := by
  intro x hx y hy hxy
  apply (div_lt_div_iff_of_pos_right (beta_mass_pos p q c)).2
  have add := intervalIntegral.integral_add_adjacent_intervals
    ((continuous_betaWeight p q c).intervalIntegrable (a := 0) (b := x) (μ := volume))
    ((continuous_betaWeight p q c).intervalIntegrable (a := x) (b := y) (μ := volume))
  linarith [beta_segment_positive p q c hx.1 hy.2 hxy]

@[simp] lemma betaCdf_zero (p q c : ℕ) : betaCdf p q c 0 = 0 := by simp [betaCdf]
@[simp] lemma betaCdf_one (p q c : ℕ) : betaCdf p q c 1 = 1 := by simp [betaCdf, (beta_mass_pos p q c).ne']

def betaMap (p q c : ℕ) (x : I) : I :=
  ⟨betaCdf p q c x, by
    have m := (betaCdf_strict p q c).monotoneOn
    exact ⟨(betaCdf_zero p q c).symm.trans_le (m (by simp) x.property x.property.1),
      (m x.property (by simp) x.property.2).trans_eq (betaCdf_one p q c)⟩⟩

lemma betaMap_surjective (p q c : ℕ) : Surjective (betaMap p q c) := by
  intro u
  have hu : (u:ℝ) ∈ Icc (betaCdf p q c 0) (betaCdf p q c 1) := by simp
  obtain ⟨t,ht,h⟩ := intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num)
    (continuous_betaCdf p q c).continuousOn hu
  exact ⟨⟨t,ht⟩, Subtype.ext h⟩

def betaIso (p q c : ℕ) : I ≃o I :=
  StrictMono.orderIsoOfSurjective (betaMap p q c)
    (fun x y h => betaCdf_strict p q c x.property y.property h) (betaMap_surjective p q c)

lemma betaQuantile_eq_inverse (p q c : ℕ) (u : I) : betaQuantile p q c u = ((betaIso p q c).symm u : ℝ) := by
  let e := betaIso p q c
  have inv : betaCdf p q c (e.symm u) = u := congrArg Subtype.val (e.apply_symm_apply u)
  unfold betaQuantile
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0,fun x hx => hx.1.1⟩
    · exact ⟨(e.symm u).property,inv.ge⟩
  · apply le_csInf
    · exact ⟨(e.symm u:ℝ),(e.symm u).property,inv.ge⟩
    · intro t ht
      exact (betaCdf_strict p q c).le_iff_le (e.symm u).property ht.1 |>.mp (inv.trans_le ht.2)

lemma uniformContinuous_quantile (p q c : ℕ) : UniformContinuous (fun u : I => betaQuantile p q c u) := by
  simp_rw [betaQuantile_eq_inverse]
  exact CompactSpace.uniformContinuous_of_continuous (continuous_subtype_val.comp (betaIso p q c).symm.continuous)

end
end LeeSah
