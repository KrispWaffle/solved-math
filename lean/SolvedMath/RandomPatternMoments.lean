import SolvedMath.RandomPatternClasses
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace DistinctPermutationPatterns
open Finset Filter
open scoped Topology
noncomputable section

def uniformAverage {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

private def truncation (w L : ℕ) : ℝ :=
  ∑ j ∈ range L, (-(1/2):ℝ)^j*(w.choose j : ℝ)

private theorem truncation_step (w L : ℕ) :
    truncation (w+1) (L+1) = truncation w (L+1) - (1/2:ℝ)*truncation w L := by
  unfold truncation
  rw [sum_range_succ',sum_range_succ' (fun j => (-(1/2):ℝ)^j*(w.choose j : ℝ)) L]
  simp only [Nat.choose_succ_succ,Nat.cast_add,mul_add,sum_add_distrib,
    Nat.choose_zero_right,Nat.cast_one,pow_zero,one_mul]
  have split : (∑ j ∈ range L, (-(1/2):ℝ)^(j+1)*(w.choose j : ℝ)) =
      (-(1/2):ℝ)*∑ j ∈ range L, (-(1/2):ℝ)^j*(w.choose j : ℝ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    rw [pow_succ]
    ring
  rw [split]
  ring

/-- A finite binomial expansion with a remainder bound valid even for arbitrarily large w. -/
theorem truncation_error (w L : ℕ) :
    |(1/2:ℝ)^w-truncation w L| ≤ (1/2:ℝ)^L * (w.choose L : ℝ) := by
  induction w generalizing L with
  | zero =>
    cases L with
    | zero => norm_num [truncation]
    | succ L => simp [truncation,sum_range_succ']
  | succ w ih =>
    cases L with
    | zero =>
      simp only [truncation,range_zero,sum_empty,sub_zero,abs_of_nonneg (by positivity : 0≤(1/2:ℝ)^(w+1)),
        pow_zero,Nat.choose_zero_right,Nat.cast_one,mul_one]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    | succ L =>
      have id : (1/2:ℝ)^(w+1)-truncation (w+1) (L+1) =
          ((1/2:ℝ)^w-truncation w (L+1)) + (-(1/2:ℝ))*((1/2:ℝ)^w-truncation w L) := by
        rw [truncation_step,pow_succ]
        ring
      rw [id]
      calc
        _ ≤ |(1/2:ℝ)^w-truncation w (L+1)|+(1/2)*|(1/2:ℝ)^w-truncation w L| := by
          simpa [abs_mul] using abs_add_le ((1/2:ℝ)^w-truncation w (L+1))
            ((-(1/2:ℝ))*((1/2:ℝ)^w-truncation w L))
        _ ≤ (1/2:ℝ)^(L+1)*(w.choose (L+1) : ℝ)+(1/2)*((1/2:ℝ)^L*(w.choose L : ℝ)) :=
          add_le_add (ih (L+1)) (mul_le_mul_of_nonneg_left (ih L) (by norm_num))
        _ = _ := by rw [Nat.choose_succ_succ,Nat.cast_add,pow_succ]; ring

private theorem average_error {α : Type*} [Fintype α] (f g h : α → ℝ)
    (hh : ∀ x, |f x-g x| ≤ h x) :
    |uniformAverage f-uniformAverage g| ≤ uniformAverage h := by
  unfold uniformAverage
  rw [←sub_div,←sum_sub_distrib,abs_div,abs_of_nonneg (by positivity : 0≤(Fintype.card α : ℝ))]
  exact div_le_div_of_nonneg_right
    ((abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun x _ => hh x))) (by positivity)

private theorem truncation_average {α : Type*} [Fintype α] (W : α → ℕ) (L : ℕ) :
    uniformAverage (fun x => truncation (W x) L) =
    ∑ j ∈ range L, (-(1/2):ℝ)^j*uniformAverage (fun x => ((W x).choose j : ℝ)) := by
  unfold uniformAverage truncation
  rw [sum_comm,sum_div]
  apply sum_congr rfl
  intro j _
  rw [←mul_sum]
  ring

private theorem weighted_error {α : Type*} [Fintype α] (W : α → ℕ) (L : ℕ) :
    |uniformAverage (fun x => (1/2:ℝ)^(W x)) -
      ∑ j ∈ range L, (-(1/2):ℝ)^j*uniformAverage (fun x => ((W x).choose j : ℝ))| ≤
      (1/2:ℝ)^L*uniformAverage (fun x => ((W x).choose L : ℝ)) := by
  rw [←truncation_average]
  apply (average_error _ _ _ (fun x => truncation_error (W x) L)).trans_eq
  unfold uniformAverage
  rw [←mul_sum]
  ring

/-- Binomial moments converging to those of Poisson(4) imply the exact half-weight mean.
The proof uses finite expansions before taking limits, so no uniform exponential moment
assumption on the finite variables is required. -/
theorem half_weight_from_binomial_moments {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)] (W : ∀ n, Ω n → ℕ)
    (hm : ∀ j : ℕ, Tendsto (fun n => uniformAverage (fun x => ((W n x).choose j : ℝ))) atTop
      (𝓝 ((4:ℝ)^j/j.factorial))) :
    Tendsto (fun n => uniformAverage (fun x => (1/2:ℝ)^(W n x))) atTop (𝓝 (Real.exp (-2))) := by
  let s := fun L : ℕ => ∑ j ∈ range L, (-2:ℝ)^j/j.factorial
  let b := fun L : ℕ => (2:ℝ)^L/L.factorial
  have hs : Tendsto s atTop (𝓝 (Real.exp (-2))) := by
    simpa only [s,Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp (-2:ℝ)).tendsto_sum_nat
  have hb : Tendsto b atTop (𝓝 0) := (NormedSpace.expSeries_div_summable (2:ℝ)).tendsto_atTop_zero
  have sc (L : ℕ) : Tendsto (fun n => ∑ j ∈ range L,
      (-(1/2):ℝ)^j*uniformAverage (fun x => ((W n x).choose j : ℝ))) atTop (𝓝 (s L)) := by
    apply tendsto_finsetSum
    intro j _
    convert (hm j).const_mul ((-(1/2):ℝ)^j) using 1
    rw [←mul_div_assoc,←mul_pow]
    norm_num
  have bc (L : ℕ) : Tendsto (fun n => (1/2:ℝ)^L*uniformAverage
      (fun x => ((W n x).choose L : ℝ))) atTop (𝓝 (b L)) := by
    convert (hm L).const_mul ((1/2:ℝ)^L) using 1
    rw [←mul_div_assoc,←mul_pow]
    norm_num [b]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ep : 0<ε/4 := by linarith
  obtain ⟨L,hL⟩ := ((Metric.tendsto_nhds.mp hs (ε/4) ep).and
    (Metric.tendsto_nhds.mp hb (ε/4) ep)).exists
  filter_upwards [Metric.tendsto_nhds.mp (sc L) (ε/4) ep, Metric.tendsto_nhds.mp (bc L) (ε/4) ep]
    with n hP hB
  simp only [Real.dist_eq,sub_zero] at hL hP hB ⊢
  have one := abs_sub_le (uniformAverage (fun x => (1/2:ℝ)^(W n x)))
    (∑ j ∈ range L, (-(1/2):ℝ)^j*uniformAverage (fun x => ((W n x).choose j : ℝ))) (s L)
  have two := abs_sub_le (uniformAverage (fun x => (1/2:ℝ)^(W n x))) (s L) (Real.exp (-2))
  linarith only [one,two,weighted_error (W n) L,hL.1,(abs_lt.mp hL.2).2,hP,(abs_lt.mp hB).2]

abbrev Sample (n : ℕ) := Equiv.Perm (Fin n) × Finset (Fin n)

/-- The actual number of individually admissible red-to-white replacements in a sampled plot. -/
def localCount {n : ℕ} (z : Sample n) : ℕ := by
  classical
  exact (univ.filter (fun ab : Fin n × Fin n =>
    ab.1∈z.2 ∧ ab.2∉z.2 ∧ ∀ x ∈ z.2, x≠ab.1 →
      ¬Between ab.1 x ab.2 ∧ ¬Between (z.1 ab.1) (z.1 x) (z.1 ab.2))).card

def classSize {n : ℕ} (z : Sample n) : ℕ := occurrenceCount z.1 (pattern z.1 z.2)

def classMismatch {n : ℕ} (z : Sample n) : ℝ := if classSize z=2^(localCount z) then 0 else 1

theorem normalizedMean_as_average (n : ℕ) :
    normalizedMean n = uniformAverage (fun z : Sample n => (classSize z : ℝ)⁻¹) := by
  rw [normalizedMean_by_occurrences,uniformAverage,Fintype.sum_prod_type]
  simp [Sample,classSize,Fintype.card_perm]

private theorem pointwise_class_error {n : ℕ} (z : Sample n) :
    |(classSize z : ℝ)⁻¹-(1/2:ℝ)^(localCount z)| ≤ classMismatch z := by
  by_cases eq : classSize z=2^localCount z
  · simp [classMismatch,eq,one_div,inv_pow]
  · rw [classMismatch,ite_eq_right eq]
    have hsize : 1≤(classSize z:ℝ) := by exact_mod_cast occurrenceCount_pos z.1 z.2
    have hinv : (classSize z:ℝ)⁻¹≤1 := inv_le_one_of_one_le₀ hsize
    have hzero : 0≤(classSize z:ℝ)⁻¹ := by positivity
    have hp : (1/2:ℝ)^localCount z ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hnon : 0≤(1/2:ℝ)^localCount z := by positivity
    exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The complete remaining combinatorial hypotheses use the actual finite permutation and
uniform subset. The conclusion is the unmodified exact expectation question from the source. -/
theorem source_limit_from_embedding_estimates
    (moments : ∀ j : ℕ, Tendsto
      (fun n => uniformAverage (fun z : Sample n => ((localCount z).choose j : ℝ))) atTop
      (𝓝 ((4:ℝ)^j/j.factorial)))
    (localization : Tendsto (fun n => uniformAverage (fun z : Sample n => classMismatch z)) atTop (𝓝 0)) :
    ExactMeanLimit := by
  have hhalf := half_weight_from_binomial_moments (fun _ z => localCount z) moments
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  have ep2 : 0<ε/2 := by linarith
  filter_upwards [Metric.tendsto_nhds.mp hhalf (ε/2) ep2,
    Metric.tendsto_nhds.mp localization (ε/2) ep2] with n h1 h2
  simp only [Real.dist_eq,sub_zero] at h1 h2 ⊢
  rw [normalizedMean_as_average]
  have hb := average_error _ _ _ (fun z : Sample n => pointwise_class_error z)
  have ha := abs_sub_le (uniformAverage (fun z : Sample n => (classSize z : ℝ)⁻¹))
    (uniformAverage (fun z : Sample n => (1/2:ℝ)^localCount z)) (Real.exp (-2))
  linarith only [ha,hb,h1,(abs_lt.mp h2).2]

end
end DistinctPermutationPatterns
