module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Concentration of the full ordered sample on a product of unit intervals, via binomial threshold counts. -/
@[expose] public section
namespace LeeSah
open Set Filter MeasureTheory ProbabilityTheory Real
open scoped NNReal unitInterval
noncomputable section

/-- Threshold indicator for an observation in the empirical distribution. -/
def below (t x : ℝ) : ℝ := if x ≤ t then 1 else 0

lemma measurable_below (t : ℝ) : Measurable (below t) :=
  Measurable.ite measurableSet_Iic measurable_const measurable_const

lemma below_unit (t x : ℝ) : below t x ∈ Icc 0 1 := by
  unfold below; split <;> constructor <;> norm_num

/-- Both one-sided Hoeffding bounds at a fixed cut, with a common mean P(X≤t).
The coefficients are valid for arbitrary finite independent samples. -/
theorem threshold_tails {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (meas : ∀ i, Measurable (X i))
    (ind : iIndepFun X μ) (t θ η : ℝ) (mean : ∀ i, ∫ ω, below t (X i ω) ∂μ = θ)
    (hη : 0 ≤ η) :
    μ.real {ω | (n:ℝ)*η ≤ (∑ i, below t (X i ω)) - n*θ} ≤ exp (-2*n*η^2) ∧
    μ.real {ω | (n:ℝ)*η ≤ n*θ - (∑ i, below t (X i ω))} ≤ exp (-2*n*η^2) := by
  let c : ℝ≥0 := (1/2)^2
  let Y (i : Fin n) (ω : Ω) := below t (X i ω) - θ
  have iy : iIndepFun Y μ := ind.comp (fun _ x => below t x - θ)
    (fun _ => (measurable_below t).sub_const θ)
  have sg (i : Fin n) : HasSubgaussianMGF (Y i) c μ := by
    have b := hasSubgaussianMGF_of_mem_Icc ((measurable_below t).comp (meas i)).aemeasurable
      (ae_of_all μ (fun ω => below_unit t (X i ω)))
    simpa [Y, c, mean] using b
  have sumSG := HasSubgaussianMGF.sum_of_iIndepFun iy (s := Finset.univ)
    (c := fun _ => c) (fun i _ => sg i)
  have upper := sumSG.measure_ge_le (ε := (n:ℝ)*η) (by positivity)
  have lower := sumSG.neg.measure_ge_le (ε := (n:ℝ)*η) (by positivity)
  have ex : -((n:ℝ)*η)^2 / (2*((n:ℝ)*((1/2)^2))) = -2*n*η^2 := by
    have hp : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  simp only [Y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Pi.neg_apply, neg_sub] at upper lower
  simp only [c, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_div,
    NNReal.coe_one, NNReal.coe_ofNat, ex] at upper lower
  exact ⟨upper,lower⟩

def ordered {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : ℝ := x (Tuple.sort x j)

/-- A coordinate of the sorted sample lies below a cut iff enough original
observations do. Ties are allowed in this deterministic lemma. -/
lemma count_iff_ordered {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    (j.val:ℝ)+1 ≤ ∑ k, below t (x k) ↔ ordered x j ≤ t := by
  classical
  rw [← Equiv.sum_comp (Tuple.sort x) (fun k => below t (x k))]
  simp only [below, Finset.sum_boole]
  exact_mod_cast (Tuple.lt_card_le_iff_apply_le_of_monotone (j := j) (a := t) (Tuple.monotone_sort x))

/-- Uniform order statistics concentrate at their one-based positions. A
union bound over the positions costs a factor n compared to sharp DKW. -/
theorem uniform_order_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (meas : ∀ i, Measurable (X i))
    (ind : iIndepFun X μ) (support : ∀ i ω, X i ω ∈ Icc 0 1)
    (mean : ∀ t ∈ Icc (0:ℝ) 1, ∀ i, ∫ ω, below t (X i ω) ∂μ = t)
    (η : ℝ) (hη : 0 < η) :
    μ.real {ω | ∃ j : Fin n, η < |ordered (fun i => X i ω) j - ((j.val:ℝ)+1)/n|}
      ≤ n * (2*exp (-2*n*η^2)) := by
  classical
  have nr : (0:ℝ) < n := by exact_mod_cast hn
  have one (j : Fin n) :
      μ.real {ω | η < |ordered (fun i => X i ω) j - ((j.val:ℝ)+1)/n|}
        ≤ 2*exp (-2*n*η^2) := by
    let u : ℝ := ((j.val:ℝ)+1)/n
    have nu : n*u=(j.val:ℝ)+1 := by dsimp [u]; field_simp
    have u0 : 0 ≤ u := by dsimp [u]; positivity
    have u1 : u ≤ 1 := by
      apply (div_le_one nr).2
      exact_mod_cast (Nat.succ_le_of_lt j.isLt)
    let y (ω : Ω) := ordered (fun i => X i ω) j
    have yr (ω : Ω) : y ω ∈ Icc 0 1 := support _ ω
    have left : μ.real {ω | y ω < u-η} ≤ exp (-2*n*η^2) := by
      by_cases ht : 0 ≤ u-η
      · have ht1 : u-η ≤ 1 := by linarith
        have H := (threshold_tails hn X meas ind (u-η) (u-η) η (mean _ ⟨ht,ht1⟩) hη.le).1
        apply le_trans (measureReal_mono ?_) H
        intro ω hw
        have ctr := (count_iff_ordered (fun i => X i ω) j (u-η)).2 (le_of_lt hw)
        change (n:ℝ)*η ≤ (∑ i, below (u-η) (X i ω)) - n*(u-η)
        rw [mul_sub,nu]; linarith
      · have empty : {ω | y ω < u-η} = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun ω =>
          not_lt_of_ge (le_trans (le_of_not_ge ht) (yr ω).1)
        rw [empty]; simp [le_of_lt (exp_pos _)]
    have right : μ.real {ω | u+η < y ω} ≤ exp (-2*n*η^2) := by
      by_cases ht : u+η ≤ 1
      · have ht0 : 0 ≤ u+η := by linarith
        have H := (threshold_tails hn X meas ind (u+η) (u+η) η (mean _ ⟨ht0,ht⟩) hη.le).2
        apply le_trans (measureReal_mono ?_) H
        intro ω hw
        have ctr := mt (count_iff_ordered (fun i => X i ω) j (u+η)).mp (not_le_of_gt hw)
        change (n:ℝ)*η ≤ n*(u+η) - (∑ i, below (u+η) (X i ω))
        rw [mul_add,nu]; linarith
      · have empty : {ω | u+η < y ω} = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun ω =>
          not_lt_of_ge (le_trans (yr ω).2 (le_of_not_ge ht))
        rw [empty]; simp [le_of_lt (exp_pos _)]
    have eh : {ω | η < |y ω - u|} ⊆ {ω | y ω < u-η} ∪ {ω | u+η < y ω} := by
      intro ω hw
      change η < |y ω - u| at hw
      rcases (lt_abs.mp hw) with h | h
      · right; change u+η < y ω; linarith
      · left; change y ω < u-η; linarith
    calc
      _ ≤ _ := measureReal_mono eh
      _ ≤ _ := measureReal_union_le _ _
      _ ≤ _ := by linarith
  have events : {ω | ∃ j : Fin n, η < |ordered (fun i => X i ω) j - ((j.val:ℝ)+1)/n|} =
      ⋃ j : Fin n, {ω | η < |ordered (fun i => X i ω) j - ((j.val:ℝ)+1)/n|} := by ext; simp
  rw [events]
  exact le_trans (measureReal_iUnion_fintype_le _) <|
    (Finset.sum_le_sum (fun j _ => one j)).trans_eq (by simp)

/-- The product-uniform probability space, with no assumptions on an empirical
measure or its concentration. -/
theorem uniform_cube_tail (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η) :
    (Measure.pi (fun _ : Fin n => (volume : Measure I))).real
      {ω | ∃ j : Fin n, η < |ordered (fun i => (ω i : ℝ)) j - ((j.val:ℝ)+1)/n|}
    ≤ n * (2*exp (-2*n*η^2)) := by
  let Q := Measure.pi (fun _ : Fin n => (volume : Measure I))
  refine uniform_order_tail (μ := Q) hn (fun i (ω : Fin n → I) => (ω i : ℝ))
    (fun i => measurable_subtype_coe.comp (measurable_pi_apply i))
    (iIndepFun_pi (fun _ => measurable_subtype_coe.aemeasurable)) (fun i ω => (ω i).property) ?_ η hη
  intro t ht i
  let τ : I := ⟨t,ht⟩
  let A : Set (Fin n → I) := Function.eval i ⁻¹' Iic τ
  have measA : MeasurableSet A := (measurable_pi_apply i) measurableSet_Iic
  have e : (fun ω : Fin n → I => below t (ω i)) = A.indicator (fun _ => (1:ℝ)) := by
    funext ω; rfl
  rw [e, integral_indicator measA, setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  have h := (measurePreserving_eval (fun _ : Fin n => (volume : Measure I)) i).measure_preimage
    measurableSet_Iic.nullMeasurableSet (s := Iic τ)
  change (Q A).toReal = t
  rw [h, unitInterval.volume_Iic, ENNReal.toReal_ofReal ht.1]

end
end LeeSah
