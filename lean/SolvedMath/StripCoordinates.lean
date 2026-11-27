import Mathlib.Algebra.LinearRecurrence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter Finset

namespace StripCoordinates

/-- Each cell in the printed strip is a translate of a cell in its vertical period. -/
abbrev Cell (rows width : ℕ) := Fin rows × Fin width

def place {n w : ℕ} (c : Cell n w) : ℤ × ℤ :=
  ((c.1 : ℤ), (c.2 : ℤ) - (c.1 : ℤ))

def earlier {n w : ℕ} (a b : Cell n w) : Prop :=
  (place a).1 ≤ (place b).1 ∧ (place a).2 ≤ (place b).2 ∧ a ≠ b

/-- The word predicate is surjectivity and the absence of a reversed strict comparison. -/
abbrev Word (n w e : ℕ) := {f : Fin (e+w*n) → Cell n w //
  Function.Surjective f ∧ ∀ i j, i < j → ¬ earlier (f j) (f i)}

private theorem earlier_level {n w : ℕ} {a b : Cell n w} (h : earlier a b) : a.2 < b.2 := by
  rcases h with ⟨h₁,h₂,hne⟩
  simp only [place] at h₁ h₂
  by_contra! h
  apply hne
  ext <;> omega

private def cut {n w e : ℕ} (t : Fin (e+(w+1)*(n+1))) : Fin ((w+1)*(n+1)) :=
  ⟨t.val-e, by
    have hp : 0 < (w+1)*(n+1) := by positivity
    have ht := t.isLt
    omega⟩

@[simp] private theorem cut_natAdd {n w e : ℕ} (t : Fin ((w+1)*(n+1))) :
    cut (Fin.natAdd e t) = t := by ext; simp [cut]

private def orderedWord {n w : ℕ} (e : ℕ) (σ : Fin (w+1) → Equiv.Perm (Fin (n+1))) :
    Word (n+1) (w+1) e := by
  let f (t : Fin (e+(w+1)*(n+1))) : Cell (n+1) (w+1) :=
    let u := finProdFinEquiv.symm (cut t)
    (σ u.1 u.2, u.1)
  refine ⟨f, ?_, ?_⟩
  · rintro ⟨i, k⟩
    refine ⟨Fin.natAdd e (finProdFinEquiv (k, (σ k).symm i)), ?_⟩
    simp only [f, cut_natAdd, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  · intro i j hij he
    have h := earlier_level he
    change (j.val-e)/(n+1) < (i.val-e)/(n+1) at h
    exact (Nat.div_le_div_right (Nat.sub_le_sub_right hij.le e)).not_gt h

private theorem orderedWord_injective {n w : ℕ} (e : ℕ) :
    Function.Injective (orderedWord (n := n) (w := w) e) := by
  intro σ τ he
  funext k
  apply Equiv.ext
  intro i
  have h := congrArg (fun f : Word (n+1) (w+1) e =>
    (f.val (Fin.natAdd e (finProdFinEquiv (k, i)))).1) he
  simpa only [orderedWord, cut_natAdd, Equiv.symm_apply_apply] using h

theorem printed_lower_bound (n w e : ℕ) :
    (n+1).factorial ^ (w+1) ≤ Nat.card (Word (n+1) (w+1) e) := by
  classical
  let _ := Fintype.ofFinite (Word (n+1) (w+1) e)
  simpa [Nat.card_eq_fintype_card, Fintype.card_pi_const, Fintype.card_perm] using
    Fintype.card_le_of_injective _ (orderedWord_injective (n := n) (w := w) e)

theorem printed_superexponential (w e a c : ℕ) :
    ∀ᶠ n in atTop, a * c^n < Nat.card (Word (n+1) (w+1) e) := by
  filter_upwards [Nat.eventually_mul_pow_lt_factorial_sub a c 0] with n hn
  have h₁ : n.factorial ≤ (n+1).factorial := Nat.factorial_le (Nat.le_succ _)
  have h₂ := Nat.le_self_pow (Nat.succ_ne_zero w) (n+1).factorial
  exact (by simpa using hn : a * c^n < n.factorial).trans_le
    (h₁.trans (h₂.trans (printed_lower_bound n w e)))

private theorem recurrence_bound {K : Type*} [NormedField K] {u : ℕ → K}
    (E : LinearRecurrence K) (hu : E.IsSolution u) :
    ∃ a c : ℕ, ∀ n, ‖u n‖ ≤ (a : ℝ) * c^n := by
  classical
  obtain ⟨a, ha⟩ := exists_nat_ge (∑ i : Fin E.order, ‖u i‖)
  obtain ⟨c, hc⟩ := exists_nat_ge (1 + ∑ i, ‖E.coeffs i‖)
  have h₁ : (1 : ℝ) ≤ c := by
    have hsum : 0 ≤ ∑ i, ‖E.coeffs i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have bound (n : ℕ) : ‖u n‖ ≤ (a : ℝ) * c^(n+1) := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      by_cases hsmall : n < E.order
      · have hle := Finset.single_le_sum (fun (i : Fin E.order) _ => norm_nonneg (u i))
          (Finset.mem_univ (⟨n,hsmall⟩ : Fin E.order))
        exact hle.trans (ha.trans (le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ h₁)))
      · let k := n-E.order
        have heq : k+E.order = n := by dsimp [k]; omega
        rw [← heq, hu]
        calc
          ‖∑ i, E.coeffs i * u (k+i)‖ ≤ ∑ i, ‖E.coeffs i * u (k+i)‖ := norm_sum_le _ _
          _ ≤ ∑ i, ‖E.coeffs i‖ * ((a : ℝ) * c^n) := by
            apply Finset.sum_le_sum
            intro i _
            have hlt : k+(i : ℕ) < n := by have hi := i.isLt; omega
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left ((ih _ hlt).trans
              (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h₁ (by omega)) (Nat.cast_nonneg _)))
              (norm_nonneg _)
          _ = (∑ i, ‖E.coeffs i‖) * ((a : ℝ) * c^n) := (Finset.sum_mul _ _ _).symm
          _ ≤ c * ((a : ℝ) * c^n) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = a * c^(k+E.order+1) := by rw [heq, pow_succ]; ring
  exact ⟨a*c,c, fun n => by simpa [Nat.cast_mul, pow_succ, mul_comm, mul_left_comm, mul_assoc] using bound n⟩

theorem printed_no_eventual_recurrence (w e shift : ℕ) (E : LinearRecurrence ℂ) :
    ¬ E.IsSolution (fun n => (Nat.card (Word (shift+n+1) (w+1) e) : ℂ)) := by
  intro hu
  obtain ⟨a,c,h⟩ := recurrence_bound E hu
  obtain ⟨n,hn⟩ := (Nat.eventually_mul_pow_lt_factorial_sub a c 0).exists
  have hsmall : a*c^n < n.factorial := by simpa using hn
  have hlarge := printed_lower_bound (shift+n) w e
  have hle := Nat.le_self_pow (Nat.succ_ne_zero w) (shift+n+1).factorial
  have hf : n.factorial ≤ (shift+n+1).factorial := Nat.factorial_le (by omega)
  have habs := h n
  rw [Complex.norm_natCast] at habs
  have hcast : Nat.card (Word (shift+n+1) (w+1) e) ≤ a*c^n := by exact_mod_cast habs
  exact (hf.trans (hle.trans (hlarge.trans hcast))).not_gt hsmall

end StripCoordinates
