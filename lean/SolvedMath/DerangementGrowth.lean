module

public import SolvedMath.DerangementRationals
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Int.Interval
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace DerangementSpectrum

open Finset Filter
open scoped Topology
noncomputable section

/-- Changing one other cell size moves the value origin relative to the position origin
by this coefficient. -/
def shiftCoefficient {n : ℕ} (τ : Perm n) (i j : Fin n) : ℤ :=
  (if τ j < τ i then 1 else 0) - (if j < i then 1 else 0)

def cellShift {n : ℕ} (τ : Perm n) (i : Fin n) (m : Fin n → ℤ) : ℤ :=
  ∑ j, shiftCoefficient τ i j * m j

@[simp] theorem shiftCoefficient_self {n : ℕ} (τ : Perm n) (i : Fin n) :
    shiftCoefficient τ i i = 0 := by simp [shiftCoefficient]

/-- Each cell of a nontrivial sum-indecomposable quotient has a nonconstant displacement. -/
theorem exists_active_cell {n : ℕ} (τ : Perm n) (hn : 2 ≤ n)
    (hτ : SumIndecomposable τ) (i : Fin n) :
    ∃ j, j ≠ i ∧ (shiftCoefficient τ i j = 1 ∨ shiftCoefficient τ i j = -1) := by
  classical
  by_contra! none
  have preds (j : Fin n) : τ j < τ i ↔ j < i := by
    by_cases hji : j = i
    · simp [hji]
    have h := none j hji
    by_cases hv : τ j < τ i
    · refine ⟨fun _ => ?_, fun _ => hv⟩
      by_contra hp
      exact h.1 (by simp [shiftCoefficient, hv, hp])
    · refine ⟨fun v => (hv v).elim, fun hp => ?_⟩
      exact (h.2 (by simp [shiftCoefficient, hv, hp])).elim
  have eqset : (Iio i).image τ = Iio (τ i) := by
    ext j
    constructor
    · intro hj
      obtain ⟨k, hk, rfl⟩ := mem_image.1 hj
      exact mem_Iio.2 ((preds k).2 (mem_Iio.1 hk))
    · intro hj
      refine mem_image.2 ⟨τ.symm j, mem_Iio.2 ?_, τ.apply_symm_apply j⟩
      exact (preds _).1 (by simpa using hj)
  have hi : (τ i).val = i.val := by
    have eq := congrArg Finset.card eqset
    simpa [card_image_of_injective _ τ.injective, Fin.card_Iio] using eq.symm
  by_cases h0 : 0 < i.val
  · apply hτ i.val h0 i.isLt
    refine ⟨i.isLt.le, fun j => ?_⟩
    have q : (τ j).val < (τ i).val ↔ j.val < i.val := preds j
    rwa [hi] at q
  · apply hτ 1 (by decide) (by omega)
    refine ⟨by omega, fun j => ?_⟩
    have hzero : i.val = 0 := by omega
    have hf : τ i = i := Fin.ext hi
    constructor
    · intro h
      have hji : τ j = τ i := Fin.ext (by omega)
      have := τ.injective hji
      simp [this, hzero]
    · intro h
      have hji : j = i := Fin.ext (by omega)
      simp [hji, hf, hzero]

/-- On a fixed-total slice of block sizes, prescribing a cell shift determines the
two sizes left free along an active direction. -/
theorem cellShift_slice_injective {n : ℕ} (τ : Perm n) (i j : Fin n)
    (hactive : shiftCoefficient τ i j ≠ 0) {m m' : Fin n → ℤ}
    (outside : ∀ k, k ≠ i → k ≠ j → m k = m' k)
    (htotal : ∑ k, m k = ∑ k, m' k) (heq : cellShift τ i m = cellShift τ i m') : m = m' := by
  classical
  have same (k : Fin n) (hk : k ∈ univ.erase j) :
      shiftCoefficient τ i k * m k = shiftCoefficient τ i k * m' k := by
    by_cases hi : k = i
    · simp [hi]
    · rw [outside k hi (ne_of_mem_erase hk)]
  have hsum := sum_congr rfl same
  unfold cellShift at heq
  rw [← sum_erase_add _ _ (mem_univ j), ← sum_erase_add _ (fun k => shiftCoefficient τ i k * m' k)
    (mem_univ j), hsum] at heq
  have hj : m j = m' j := by
    exact mul_left_cancel₀ hactive (add_left_cancel heq)
  have rest (k : Fin n) (hk : k ∈ univ.erase i) : m k = m' k := by
    by_cases h : k = j
    · simpa [h] using hj
    · exact outside k (ne_of_mem_erase hk) h
  have hsum' := sum_congr rfl rest
  rw [← sum_erase_add _ _ (mem_univ i), ← sum_erase_add _ m' (mem_univ i), hsum'] at htotal
  funext k
  by_cases hi : k = i
  · simpa [hi] using add_left_cancel htotal
  · exact rest k (mem_erase.2 ⟨hi, mem_univ k⟩)

/-- Each fixed-total fibre of the slab has at most 2L+1 integer points. -/
theorem cellShift_slab_card {n : ℕ} (τ : Perm n) (i j : Fin n)
    (hactive : shiftCoefficient τ i j ≠ 0) (L : ℕ) (fibre : Finset (Fin n → ℤ))
    (outside : ∀ m ∈ fibre, ∀ m' ∈ fibre, ∀ k, k ≠ i → k ≠ j → m k = m' k)
    (totals : ∀ m ∈ fibre, ∀ m' ∈ fibre, ∑ k, m k = ∑ k, m' k)
    (slab : ∀ m ∈ fibre, cellShift τ i m ∈ Finset.Icc (-(L : ℤ)) L) :
    fibre.card ≤ 2*L+1 := by
  have bound := card_le_card_of_injOn (cellShift τ i) slab
    (fun m hm m' hm' heq => cellShift_slice_injective τ i j hactive
      (outside m hm m' hm') (totals m hm m' hm') heq)
  rw [Int.card_Icc] at bound
  omega

private def digit (d : ℕ) (x : ℝ) := min d ⌊x⌋₊

private def remainder (d : ℕ) (z x : ℝ) : ℕ → ℝ
  | 0 => x
  | n+1 => (remainder d z x n - digit d (remainder d z x n)) / z

private theorem digit_step {d : ℕ} {z U x : ℝ} (hz : 0 < z) (cover : 1 ≤ z*U)
    (endpt : (d:ℝ) + z*U = U) (hx : x ∈ Set.Icc 0 U) :
    (x - digit d x) / z ∈ Set.Icc 0 U := by
  have hf := Nat.floor_le hx.1
  have hl := Nat.lt_floor_add_one x
  have bound : (digit d x : ℝ) ≤ x := by
    exact (show (digit d x : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast min_le_right _ _).trans hf
  refine ⟨div_nonneg (sub_nonneg.mpr bound) hz.le, (div_le_iff₀ hz).2 ?_⟩
  by_cases h : d ≤ ⌊x⌋₊
  · rw [digit, min_eq_left h]
    linarith [hx.2]
  · rw [digit, min_eq_right (le_of_not_ge h)]
    linarith

/-- Every value in the full digit interval is an actual convergent series, including
both endpoints and the case where consecutive digit intervals only touch. -/
theorem geometric_digit_interval {d : ℕ} {z x : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (cover : 1-z ≤ (d:ℝ)*z) (hx : x ∈ Set.Icc 0 ((d:ℝ)/(1-z))) :
    ∃ digits : ℕ → Fin (d+1), HasSum (fun j => ((digits j).val : ℝ)*z^j) x := by
  let U : ℝ := d/(1-z)
  have hp : 0 < 1-z := sub_pos.mpr hz1
  have hden : U*(1-z) = d := div_mul_cancel₀ _ hp.ne'
  have hcover : 1 ≤ z*U := by
    rw [show z*U = ((d:ℝ)*z)/(1-z) by dsimp [U]; ring]
    exact (le_div_iff₀ hp).2 (by simpa using cover)
  have endpt : (d:ℝ)+z*U = U := by nlinarith
  have hr (n : ℕ) : remainder d z x n ∈ Set.Icc 0 U := by
    induction n with
    | zero => exact hx
    | succ n ih => exact digit_step hz hcover endpt ih
  let digits (j : ℕ) : Fin (d+1) := ⟨digit d (remainder d z x j),
    Nat.lt_succ_of_le (min_le_left _ _)⟩
  refine ⟨digits, (hasSum_iff_tendsto_nat_of_nonneg (fun j =>
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz.le j)) x).2 ?_⟩
  have e (n : ℕ) :
      (∑ j ∈ range n, ((digits j).val : ℝ)*z^j) + z^n * remainder d z x n = x := by
    induction n with
    | zero => simp [remainder]
    | succ n ih =>
      have back : z * remainder d z x (n+1) =
          remainder d z x n - (digits n).val := by
        change z * ((remainder d z x n - (digit d (remainder d z x n) : ℝ)) / z) = _
        rw [mul_comm, div_mul_cancel₀ _ hz.ne']
      rw [sum_range_succ, pow_succ, mul_assoc, back]
      linarith only [ih, mul_sub (z^n) (remainder d z x n) ((digits n).val : ℝ),
        mul_comm (z^n) ((digits n).val : ℝ)]
  have hlim : Tendsto (fun n => z^n * remainder d z x n) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => mul_nonneg (pow_nonneg hz.le _) (hr n).1)
      (fun n => mul_le_mul_of_nonneg_left (hr n).2 (pow_nonneg hz.le n))
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hz.le hz1).mul_const U
  have lim := (tendsto_const_nhds (x := x)).sub hlim
  rw [sub_zero] at lim
  exact lim.congr (fun n => by have := e n; linarith)

/-- Starting immediately after size m, the optional tags fill every residual left
by a greedy choice of size-m indecomposables. -/
theorem fill_tail_weight {d m : ℕ} {z x : ℝ} (hz : 0 < z) (hz1 : z < 1)
    (cover : 1-z ≤ (d:ℝ)*z) (hx : x ∈ Set.Icc 0 (z^m)) :
    ∃ e : ℕ → Fin (d+1), HasSum (fun k => ((e k).val:ℝ)*z^(m+1+k)) x := by
  have hpow : 0 < z^(m+1) := pow_pos hz _
  have hU : x / z^(m+1) ≤ (d:ℝ)/(1-z) := by
    apply (div_le_div_iff₀ hpow (sub_pos.mpr hz1)).2
    rw [pow_succ]
    calc
      x*(1-z) ≤ z^m*(1-z) := mul_le_mul_of_nonneg_right hx.2 (sub_nonneg.mpr hz1.le)
      _ ≤ z^m*((d:ℝ)*z) := mul_le_mul_of_nonneg_left cover (pow_nonneg hz.le _)
      _ = (d:ℝ)*(z^m*z) := by ring
  obtain ⟨e, he⟩ := geometric_digit_interval hz hz1 cover ⟨div_nonneg hx.1 hpow.le, hU⟩
  refine ⟨e, ?_⟩
  have scaled := he.mul_right (z^(m+1))
  rw [div_mul_cancel₀ _ hpow.ne'] at scaled
  convert scaled using 1
  funext k
  rw [pow_add]
  ring

/-- Solve the actual ratio of the leading weights using finitely many distinct labels
and one suffix weight chosen in a fixed interval. -/
theorem prescribe_mixture {p H Z δ : ℝ} (hp : 0 < p) (hp1 : p < 1) (hZ : 0 < Z)
    (hδ : 0 < δ) :
    ∃ (a b M : ℕ) (t : ℝ), 0 < M ∧ t ∈ Set.Icc 0 δ ∧
      ((a:ℝ) + M*H) / (a + b + M*(Z+t)) = p := by
  obtain ⟨M, hM⟩ := exists_nat_gt (1/δ)
  have hMpos : (0:ℝ) < M := (one_div_pos.mpr hδ).trans hM
  let q := (1-p)/p
  have hq : 0 < q := div_pos (sub_pos.mpr hp1) hp
  let C := (M:ℝ)*(H/p-Z)
  obtain ⟨a, ha⟩ := exists_nat_gt (-C/q)
  have hT : 0 ≤ q*(a:ℝ)+C := by
    have := (div_lt_iff₀ hq).mp ha
    linarith
  let T := q*(a:ℝ)+C
  let b := ⌊T⌋₊
  let t := (T-b)/M
  have hfloor : (b:ℝ) ≤ T := Nat.floor_le hT
  have hceil : T < b+1 := Nat.lt_floor_add_one _
  have htn : 0 ≤ t := div_nonneg (sub_nonneg.mpr hfloor) hMpos.le
  have hmuster := (div_lt_iff₀ hδ).mp hM
  have htu : t ≤ δ := (div_le_iff₀ hMpos).2 (by linarith)
  have denom : (0:ℝ) < a + b + M*(Z+t) :=
    add_pos_of_nonneg_of_pos (by positivity) (mul_pos hMpos (add_pos_of_pos_of_nonneg hZ htn))
  refine ⟨a, b, M, t, by exact_mod_cast hMpos, ⟨htn, htu⟩, (div_eq_iff denom.ne').2 ?_⟩
  have eq : (M:ℝ)*t = T-b := by dsimp [t]; field_simp
  dsimp [T, q, C] at eq
  field_simp [hp.ne'] at eq
  nlinarith only [eq]

/-- Both ordinary limits belong to the same infinite hereditary class. -/
def AttainedAtGrowth (p g : ℝ) : Prop :=
  ∃ C : PermutationClass, (∀ n, (C.slice n).Nonempty) ∧
    Tendsto (ratio C) atTop (𝓝 p) ∧
    Tendsto (fun n => (total C n : ℝ)^((n:ℝ)⁻¹)) atTop (𝓝 g)

theorem ratio_limit_of_scaled_counts (C : PermutationClass) (s : ℕ → ℝ)
    {D T : ℝ} (hs : ∀ᶠ n in atTop, s n ≠ 0) (hT : T ≠ 0)
    (hfree : Tendsto (fun n => (free C n : ℝ)/s n) atTop (𝓝 D))
    (htotal : Tendsto (fun n => (total C n : ℝ)/s n) atTop (𝓝 T)) :
    Tendsto (ratio C) atTop (𝓝 (D/T)) := by
  apply (hfree.div htotal hT).congr'
  filter_upwards [hs] with n hn
  dsimp [ratio]
  field_simp

/-- The written inflation estimates give the three kinds of labelled classes below.
The parameter choice and conclusion use the original, all-length notion of growth. -/
theorem fixed_growth_spectrum_of_labelled_classes {g H Z δ : ℝ} (hZ : 0 < Z)
    (hδ : 0 < δ) (hzero : AttainedAtGrowth 0 g) (hone : AttainedAtGrowth 1 g)
    (labels : ∀ (a b M : ℕ), 0 < M → ∀ t ∈ Set.Icc 0 δ,
      AttainedAtGrowth (((a:ℝ)+M*H)/(a+b+M*(Z+t))) g) :
    ∀ p ∈ Set.Icc (0:ℝ) 1, AttainedAtGrowth p g := by
  intro p hp
  obtain rfl | hpos := eq_or_lt_of_le hp.1
  · exact hzero
  obtain rfl | hlt := eq_or_lt_of_le hp.2
  · exact hone
  obtain ⟨a, b, M, t, hM, ht, rfl⟩ := prescribe_mixture hpos hlt hZ hδ (H := H)
  exact labels a b M hM t ht

end
end DerangementSpectrum
