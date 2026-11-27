import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open Filter Finset Real
open scoped Topology

namespace ShiftedGrid

noncomputable section

def angle (x : ℝ) := (π / 2) / x

def rate (x : ℝ) := log 2 - x * log (2 * sin (angle x))

def slope (x : ℝ) := -log (2 * sin (angle x)) + angle x * cos (angle x) / sin (angle x)

private theorem angle_pos {x : ℝ} (hx : 2 ≤ x) : 0 < angle x := by
  unfold angle
  positivity

private theorem sin_angle_pos {x : ℝ} (hx : 2 ≤ x) : 0 < sin (angle x) := by
  apply sin_pos_of_pos_of_lt_pi (angle_pos hx)
  change π / 2 / x < π
  rw [div_lt_iff₀ (by linarith : 0 < x)]
  nlinarith [pi_pos, mul_nonneg pi_pos.le (sub_nonneg.mpr hx)]

private theorem angle_derivative {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt angle (-angle x / x) x := by
  have hx0 : x ≠ 0 := by linarith
  convert (hasDerivAt_const x (π / 2)).div (hasDerivAt_id x) hx0 using 1
  · rfl
  · simp only [angle, id_eq]
    field_simp
    ring

private theorem log_derivative {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt (fun y => log (2 * sin (angle y)))
      (cos (angle x) * (-angle x / x) / sin (angle x)) x := by
  have hs := (sin_angle_pos hx).ne'
  convert (((angle_derivative hx).sin.const_mul 2).log (mul_ne_zero (by norm_num) hs)) using 1
  field_simp

theorem rate_derivative {x : ℝ} (hx : 2 ≤ x) : HasDerivAt rate (slope x) x := by
  have hx0 : x ≠ 0 := by linarith
  have hs := (sin_angle_pos hx).ne'
  convert (hasDerivAt_const x (log 2)).sub ((hasDerivAt_id x).mul (log_derivative hx)) using 1
  · rfl
  · simp only [slope, id_eq]
    field_simp
    ring

theorem slope_derivative {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt slope ((angle x)^2 / (x * sin (angle x)^2)) x := by
  have hx0 : x ≠ 0 := by linarith
  have hs := (sin_angle_pos hx).ne'
  have ht := angle_derivative hx
  convert (log_derivative hx).neg.add ((ht.mul ht.cos).div ht.sin hs) using 1
  · rfl
  · simp only [Pi.mul_apply]
    field_simp
    linear_combination -((angle x)^2) * sin_sq_add_cos_sq (angle x)

theorem slope_strictMono : StrictMonoOn slope (Set.Ici 2) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) (fun x hx => (slope_derivative hx).continuousAt.continuousWithinAt) ?_
  intro x hx
  have h := interior_subset hx
  rw [(slope_derivative h).deriv]
  exact div_pos (sq_pos_of_pos (angle_pos h)) (mul_pos (by change 2 ≤ x at h; linarith) (sq_pos_of_pos (sin_angle_pos h)))

theorem increment_strictMono {v : ℝ} (hv : 0 < v) :
    StrictMonoOn (fun x => rate (x+v) - rate x) (Set.Ici 2) := by
  have hd (x : ℝ) (hx : 2 ≤ x) :
      HasDerivAt (fun y => rate (y+v) - rate y) (slope (x+v) - slope x) x := by
    have h := (rate_derivative (show 2 ≤ x + v by linarith)).comp x ((hasDerivAt_id x).add_const v)
    simpa only [id_eq, mul_one, Function.comp_def, Pi.sub_def] using h.sub (rate_derivative hx)
  apply strictMonoOn_of_deriv_pos (convex_Ici _)
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 2 ≤ x := interior_subset hx
    rw [(hd x hx').deriv, sub_pos]
    exact slope_strictMono hx' (by change 2 ≤ x + v; linarith) (by linarith)

theorem rate_four_point {x y u v : ℝ} (hx : 2 ≤ x+u) (hxy : x < y) (huv : u < v) :
    rate (x+v) + rate (y+u) < rate (x+u) + rate (y+v) := by
  have h := increment_strictMono (sub_pos.mpr huv)
    (show x+u ∈ Set.Ici 2 from hx) (show y+u ∈ Set.Ici 2 by change 2 ≤ y+u; linarith)
    (show x+u < y+u by linarith)
  dsimp at h
  rw [show x+u+(v-u)=x+v by ring, show y+u+(v-u)=y+v by ring] at h
  linarith

def score {d : ℕ} (F : Fin d → Fin d → ℝ) (σ : Equiv.Perm (Fin d)) : ℝ :=
  ∑ i, F (σ i) i

private theorem swap_improves {d : ℕ} {F : Fin d → Fin d → ℝ}
    (hF : ∀ i j k l, i < j → k < l → F i l + F j k < F i k + F j l)
    (σ : Equiv.Perm (Fin d)) {i j : Fin d} (hij : i < j) (hinv : σ j < σ i) :
    score F σ < score F ((Equiv.swap i j).trans σ) := by
  classical
  have hi : i ∈ (univ : Finset (Fin d)) := mem_univ _
  have hj : j ∈ (univ : Finset (Fin d)).erase i := mem_erase.mpr ⟨hij.ne', mem_univ _⟩
  simp only [score, ← univ.sum_erase_add _ hi, ← (univ.erase i).sum_erase_add _ hj,
    add_assoc, Equiv.coe_trans, Function.comp_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
  apply add_lt_add_of_le_of_lt
  · exact (sum_congr rfl fun k hk => by
      rw [Equiv.swap_apply_of_ne_of_ne (mem_erase.mp (mem_erase.mp hk).2).1 (mem_erase.mp hk).1]).le
  · linarith [hF (σ j) (σ i) i j hinv hij]

theorem identity_unique_max {d : ℕ} {F : Fin d → Fin d → ℝ}
    (hF : ∀ i j k l, i < j → k < l → F i l + F j k < F i k + F j l)
    {σ : Equiv.Perm (Fin d)} (hσ : σ ≠ 1) : score F σ < score F 1 := by
  classical
  have improve (τ : Equiv.Perm (Fin d)) (hne : τ ≠ 1) : ∃ υ, score F τ < score F υ := by
    by_contra! hn
    apply hne
    have hm : StrictMono τ := by
      intro i j hij
      apply lt_of_not_ge
      intro h
      have hlt : τ j < τ i := lt_of_le_of_ne h (fun he => hij.ne (τ.injective he.symm))
      exact (hn _).not_gt (swap_improves hF τ hij hlt)
    exact Equiv.ext (congrFun hm.eq_id)
  obtain ⟨τ, _, hτ⟩ := univ.exists_max_image (score F) univ_nonempty
  have he : τ = 1 := by
    by_contra hn
    obtain ⟨υ, hu⟩ := improve τ hn
    exact (hτ υ (mem_univ _)).not_gt hu
  subst τ
  obtain ⟨υ, hu⟩ := improve σ hσ
  exact hu.trans_le (hτ υ (mem_univ _))

def term {d : ℕ} (A : ℕ → Matrix (Fin d) (Fin d) ℝ) (σ : Equiv.Perm (Fin d)) (m : ℕ) : ℝ :=
  ∏ i, A m (σ i) i

private theorem term_pos {d : ℕ} {A : ℕ → Matrix (Fin d) (Fin d) ℝ}
    (hA : ∀ m i j, 0 < A m i j) (σ : Equiv.Perm (Fin d)) (m : ℕ) : 0 < term A σ m :=
  prod_pos fun i _ => hA m (σ i) i

private theorem log_term_limit {d : ℕ} {A : ℕ → Matrix (Fin d) (Fin d) ℝ}
    {F : Fin d → Fin d → ℝ} (hA : ∀ m i j, 0 < A m i j)
    (hlim : ∀ i j, Tendsto (fun m : ℕ => log (A m i j) / m) atTop (𝓝 (F i j)))
    (σ : Equiv.Perm (Fin d)) :
    Tendsto (fun m : ℕ => log (term A σ m) / m) atTop (𝓝 (score F σ)) := by
  unfold score term
  simpa only [log_prod (fun i _ => (hA _ (σ i) i).ne'), sum_div] using
    tendsto_finsetSum univ (fun i _ => hlim (σ i) i)

private theorem term_ratio_limit {d : ℕ} {A : ℕ → Matrix (Fin d) (Fin d) ℝ}
    {F : Fin d → Fin d → ℝ} (hA : ∀ m i j, 0 < A m i j)
    (hlim : ∀ i j, Tendsto (fun m : ℕ => log (A m i j) / m) atTop (𝓝 (F i j)))
    (σ : Equiv.Perm (Fin d)) (hscore : score F σ < score F 1) :
    Tendsto (fun m => term A σ m / term A 1 m) atTop (𝓝 0) := by
  have hdiff := (log_term_limit hA hlim σ).sub (log_term_limit hA hlim 1)
  have hbot := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_neg (sub_neg.mpr hscore) hdiff
  apply (tendsto_exp_atBot.comp hbot).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hs := term_pos hA σ m
  have hi := term_pos hA 1 m
  change exp ((m : ℝ) * (log (term A σ m) / m - log (term A 1 m) / m)) = _
  rw [← sub_div, mul_div_cancel₀ _ hm', ← log_div hs.ne' hi.ne', exp_log (div_pos hs hi)]

theorem normalized_det_limit {d : ℕ} {A : ℕ → Matrix (Fin d) (Fin d) ℝ}
    {F : Fin d → Fin d → ℝ} (hA : ∀ m i j, 0 < A m i j)
    (hlim : ∀ i j, Tendsto (fun m : ℕ => log (A m i j) / m) atTop (𝓝 (F i j)))
    (hF : ∀ i j k l, i < j → k < l → F i l + F j k < F i k + F j l) :
    Tendsto (fun m => (A m).det / term A 1 m) atTop (𝓝 1) := by
  classical
  let sign (σ : Equiv.Perm (Fin d)) : ℝ := ((Equiv.Perm.sign σ : ℤ) : ℝ)
  have oneTerm (σ : Equiv.Perm (Fin d)) :
      Tendsto (fun m => sign σ * (term A σ m / term A 1 m)) atTop (𝓝 (if σ = 1 then 1 else 0)) := by
    by_cases he : σ = 1
    · subst σ
      simp [sign, (term_pos hA 1 _).ne']
    · simpa [he] using (term_ratio_limit hA hlim σ (identity_unique_max hF he)).const_mul (sign σ)
  have hsum := tendsto_finsetSum univ (fun σ _ => oneTerm σ)
  simpa [Matrix.det_apply', term, Finset.sum_div, mul_div_assoc, sign] using hsum

/-- Positive arrays with the strip's entrywise log growth have eventually positive fixed minors. -/
theorem eventual_positive_minor {d : ℕ} {a b : Fin d → ℕ}
    (ha : StrictMono a) (hb : StrictMono b) (G : ℕ → ℕ → ℝ) (hG : ∀ m r, 0 < G m r)
    (hlim : ∀ r, Tendsto (fun m : ℕ => log (G m r) / m) atTop (𝓝 (rate ((r : ℝ)+2)))) :
    ∀ᶠ m in atTop, 0 < (Matrix.of (fun i j => G m (a i + b j))).det := by
  let A (m : ℕ) : Matrix (Fin d) (Fin d) ℝ := Matrix.of (fun i j => G m (a i + b j))
  let F (i j : Fin d) : ℝ := rate (((a i + b j : ℕ) : ℝ) + 2)
  have hA (m i j) : 0 < A m i j := hG _ _
  have hF (i j k l : Fin d) (hij : i < j) (hkl : k < l) :
      F i l + F j k < F i k + F j l := by
    have h := rate_four_point (x := (a i : ℝ) + 2) (y := (a j : ℝ) + 2)
      (u := (b k : ℝ)) (v := (b l : ℝ)) (by linarith [Nat.cast_nonneg (α := ℝ) (a i), Nat.cast_nonneg (α := ℝ) (b k)])
      (by exact_mod_cast Nat.add_lt_add_right (ha hij) 2) (by exact_mod_cast hb hkl)
    simpa [F, add_right_comm] using h
  have h := normalized_det_limit hA (fun i j => hlim (a i + b j)) hF
  filter_upwards [h.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with m hm
  exact (div_pos_iff_of_pos_right (term_pos hA 1 m)).mp hm

private theorem convex_four_point {f : ℝ → ℝ} (hf : StrictConvexOn ℝ (Set.Ici 0) f)
    {x y u v : ℝ} (hl : 0 ≤ x+u) (hxy : x < y) (huv : u < v) :
    f (x+v) + f (y+u) < f (x+u) + f (y+v) := by
  have hr : 0 ≤ y+v := by linarith
  have h₁ := hf.secant_strict_mono_aux1 hl hr (y := x+v) (by linarith) (by linarith)
  have h₂ := hf.secant_strict_mono_aux1 hl hr (y := y+u) (by linarith) (by linarith)
  apply lt_of_mul_lt_mul_left (a := (y+v)-(x+u)) _ (by linarith)
  linarith only [h₁, h₂]

private def centering (V c : ℝ) (s : ℕ) (z : ℕ) : ℝ :=
  exp (-((z : ℝ) * s * (V * log s + c)))

private theorem centered_log_limit {G : ℕ → ℝ} (hpos : ∀ r, 0 < G r) (hzero : G 0 = 1)
    {V c : ℝ}
    (hrate : Tendsto (fun r : ℕ => (log (G r) - V * r * log r) / r) atTop (𝓝 c))
    (z : ℕ) : Tendsto (fun s : ℕ => log (centering V c s z * G (s*z)) / s) atTop
      (𝓝 (V * (z * log z))) := by
  cases eq_or_ne z 0 with
  | inl he =>
    subst z
    simp [centering, hzero]
  | inr hz =>
    have hz' : (z : ℝ) ≠ 0 := by exact_mod_cast hz
    have ht : Tendsto (fun s : ℕ => s*z) atTop atTop := by
      apply tendsto_atTop_mono (fun s => Nat.le_mul_of_pos_right s (Nat.pos_of_ne_zero hz)) tendsto_id
    have h := ((hrate.comp ht).sub_const c).const_mul (z : ℝ)
    have h' := h.add_const (V * (z * log z))
    simp only [sub_self, mul_zero, zero_add] at h'
    apply h'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with s hs
    have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
    simp only [Function.comp_apply, Nat.cast_mul, centering, log_mul (exp_pos _).ne' (hpos _).ne',
      log_exp, log_mul hs' hz']
    field_simp
    ring

/-- A factorial-growth expansion implies eventual positivity under dilation, for every fixed minor. -/
theorem eventual_positive_dilated_minor {d : ℕ} {a b : Fin d → ℕ}
    (ha : StrictMono a) (hb : StrictMono b) {G : ℕ → ℝ} (hpos : ∀ r, 0 < G r)
    (hzero : G 0 = 1) {V c : ℝ} (hV : 0 < V)
    (hrate : Tendsto (fun r : ℕ => (log (G r) - V * r * log r) / r) atTop (𝓝 c)) :
    ∀ᶠ s : ℕ in atTop, 0 < (Matrix.of (fun i j => G (s*(a i+b j)))).det := by
  let M (s : ℕ) : Matrix (Fin d) (Fin d) ℝ := Matrix.of (fun i j => G (s*(a i+b j)))
  let A (s : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
    Matrix.of (fun i j => centering V c s (a i + b j) * G (s*(a i+b j)))
  let F (i j : Fin d) : ℝ := V * (((a i + b j : ℕ) : ℝ) * log ((a i + b j : ℕ) : ℝ))
  have hA (s i j) : 0 < A s i j := mul_pos (exp_pos _) (hpos _)
  have hF (i j k l : Fin d) (hij : i < j) (hkl : k < l) : F i l + F j k < F i k + F j l := by
    have h := convex_four_point strictConvexOn_mul_log (x := (a i : ℝ)) (y := (a j : ℝ))
      (u := (b k : ℝ)) (v := (b l : ℝ)) (by positivity)
      (by exact_mod_cast ha hij) (by exact_mod_cast hb hkl)
    simpa [F, mul_add] using (mul_lt_mul_of_pos_left h hV)
  have hd := normalized_det_limit hA (fun i j => centered_log_limit hpos hzero hrate (a i + b j)) hF
  filter_upwards [hd.eventually (lt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with s hs
  have hdet := (div_pos_iff_of_pos_right (term_pos hA 1 s)).mp hs
  have hfact : A s = Matrix.diagonal (fun i => centering V c s (a i)) * M s *
      Matrix.diagonal (fun j => centering V c s (b j)) := by
    ext i j
    simp only [A, M, Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, centering, Nat.cast_add]
    rw [show -(((a i : ℝ) + (b j : ℝ)) * s * (V * log s + c)) =
      -((a i : ℝ) * s * (V * log s + c)) + -((b j : ℝ) * s * (V * log s + c)) by ring, exp_add]
    ring
  rw [hfact, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal] at hdet
  have hleft : 0 < ∏ i, centering V c s (a i) := prod_pos fun _ _ => exp_pos _
  have hright : 0 < ∏ i, centering V c s (b i) := prod_pos fun _ _ => exp_pos _
  exact (mul_pos_iff_of_pos_left hleft).mp ((mul_pos_iff_of_pos_right hright).mp hdet)

#print axioms eventual_positive_dilated_minor

end

#print axioms eventual_positive_minor

end ShiftedGrid
