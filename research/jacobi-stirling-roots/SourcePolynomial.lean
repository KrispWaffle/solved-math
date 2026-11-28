import ExtremeRoots
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Roots

namespace JacobiStirlingExtreme

open Polynomial Finset Filter
open scoped Topology
noncomputable section

private def geometric (a : ℕ[X]) : PowerSeries ℕ[X] := PowerSeries.mk (fun m => a^m)
private def alphabetSeries (n : ℕ) : PowerSeries ℕ[X] :=
  ∏ j : Fin n, geometric (letter (j.val+1))

private theorem histogram_coeff (k n : ℕ) :
    diagonal k n = PowerSeries.coeff k (alphabetSeries n) := by
  classical
  rw [diagonal, ← sum_filter, alphabetSeries, PowerSeries.coeff_prod]
  let encode (m : Fin n → Fin (k+1)) : Fin n →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun j => (m j).val)
  have encoded (m : Fin n → Fin (k+1)) (j : Fin n) : encode m j = (m j).val := rfl
  apply Finset.sum_bij (fun m _ => encode m)
  · intro m hm
    exact mem_finsuppAntidiag.mpr ⟨(mem_filter.mp hm).2,subset_univ _⟩
  · intro m _ q _ eq
    funext j
    exact Fin.ext (congrArg (fun f : Fin n →₀ ℕ => f j) eq)
  · intro f hf
    have size := (mem_finsuppAntidiag.mp hf).1
    let m (j : Fin n) : Fin (k+1) := ⟨f j, by
      exact Nat.lt_succ_of_le ((Finset.single_le_sum (fun l _ => Nat.zero_le (f l))
        (mem_univ j)).trans_eq size)⟩
    refine ⟨m,mem_filter.mpr ⟨mem_univ _,size⟩,?_⟩
    ext j
    exact encoded m j
  · intro m _
    simp only [geometric, PowerSeries.coeff_mk, encoded]

private theorem geometric_step (a : ℕ[X]) :
    geometric a = 1 + PowerSeries.X * (PowerSeries.C a * geometric a) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [geometric]
  | succ n => simp [geometric, PowerSeries.coeff_succ_X_mul, pow_succ, mul_comm]

private theorem alphabet_succ (n : ℕ) :
    alphabetSeries (n+1) = alphabetSeries n * geometric (letter (n+1)) := by
  simp [alphabetSeries,Fin.prod_univ_castSucc]

/-- The complete-homogeneous definition obeys the original Jacobi–Stirling diagonal recurrence. -/
theorem diagonal_step (k n : ℕ) : diagonal (k+1) (n+1) =
    diagonal (k+1) n + letter (n+1) * diagonal k (n+1) := by
  have h : alphabetSeries (n+1) = alphabetSeries n +
      PowerSeries.X * (PowerSeries.C (letter (n+1)) * alphabetSeries (n+1)) := by
    rw [alphabet_succ]
    calc
      _ = alphabetSeries n * (1 + PowerSeries.X *
          (PowerSeries.C (letter (n+1)) * geometric (letter (n+1)))) :=
        congrArg (alphabetSeries n * ·) (geometric_step _)
      _ = _ := by ring
  simpa only [histogram_coeff,map_add,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_C_mul]
    using congrArg (PowerSeries.coeff (k+1)) h

private theorem diagonal_no_letters (k : ℕ) : diagonal (k+1) 0 = 0 := by
  rw [histogram_coeff]
  simp [alphabetSeries]

private theorem diagonal_empty (n : ℕ) : diagonal 0 n = 1 := by
  rw [histogram_coeff,PowerSeries.coeff_zero_eq_constantCoeff]
  simp [alphabetSeries,geometric]

private theorem coeff_step_zero (k n : ℕ) : coeff (k+1) 0 (n+1) =
    coeff (k+1) 0 n + (n+1)*((n+1)*coeff k 0 (n+1)) := by
  simp [coeff,diagonal_step,letter,mul_assoc,add_mul]

private theorem coeff_step_succ (k i n : ℕ) : coeff (k+1) (i+1) (n+1) =
    coeff (k+1) (i+1) n + (n+1)*((n+1)*coeff k (i+1) (n+1)) + (n+1)*coeff k i (n+1) := by
  simp [coeff,diagonal_step,letter,mul_assoc,add_mul,mul_add]
  ring

/-- Finite nonnegative combinations of n choose j with j at most d. -/
private inductive BinSpan (d : ℕ) : (ℕ → ℕ) → Prop
  | term (a j : ℕ) (h : j ≤ d) : BinSpan d (fun n : ℕ => a*n.choose j)
  | add {f g : ℕ → ℕ} : BinSpan d f → BinSpan d g → BinSpan d (fun n => f n + g n)

private theorem bin_mono {d e : ℕ} {f : ℕ → ℕ} (h : BinSpan d f) (hle : d ≤ e) : BinSpan e f := by
  induction h with
  | term a j hj => exact .term a j (hj.trans hle)
  | add _ _ ih jh => exact .add ih jh

private theorem bin_zero (d : ℕ) : BinSpan d (fun _ => 0) := by
  simpa using BinSpan.term (d := d) 0 0 (Nat.zero_le _)

private theorem times_index {d : ℕ} {f : ℕ → ℕ} (h : BinSpan d f) :
    BinSpan (d+1) (fun n => n*f n) := by
  induction h with
  | term a j hj =>
    have basis (n : ℕ) : n*n.choose j = j*n.choose j + (j+1)*n.choose (j+1) := by
      have e := Nat.add_one_mul_choose_eq n j
      rw [Nat.choose_succ_succ] at e
      nlinarith only [e]
    convert BinSpan.add (BinSpan.term (a*j) j (by omega : j≤d+1))
      (BinSpan.term (a*(j+1)) (j+1) (by omega : j+1≤d+1)) using 1
    funext n
    dsimp
    nlinarith only [congrArg (a * ·) (basis n)]
  | add _ _ ih jh => simpa only [Nat.mul_add] using BinSpan.add ih jh

private theorem choose_prefix (n j : ℕ) : (∑ m ∈ range (n+1), m.choose j) = (n+1).choose (j+1) := by
  induction n with
  | zero =>
    cases j with
    | zero => simp
    | succ j => simp [Nat.choose_eq_zero_of_lt (show 1 < j+1+1 by omega)]
  | succ n ih =>
    rw [sum_range_succ,ih,Nat.choose_succ_succ (n+1) j]
    exact Nat.add_comm _ _

private theorem prefix_span {d : ℕ} {f : ℕ → ℕ} (h : BinSpan d f) :
    BinSpan (d+1) (fun n => ∑ m ∈ range (n+1), f m) := by
  induction h with
  | term a j hj =>
    convert BinSpan.add (BinSpan.term a j (by omega : j≤d+1))
      (BinSpan.term a (j+1) (by omega : j+1≤d+1)) using 1
    funext n
    simp only [← Finset.mul_sum, choose_prefix,Nat.choose_succ_succ,Nat.mul_add]
  | add _ _ ih jh => simpa only [Finset.sum_add_distrib] using BinSpan.add ih jh

private theorem prefix_of_step {f g : ℕ → ℕ} (hf : f 0 = 0) (hg : g 0 = 0)
    (h : ∀ n, f (n+1) = f n + g (n+1)) : f = fun n => ∑ m ∈ range (n+1), g m := by
  funext n
  induction n with
  | zero => simp [hf,hg]
  | succ n ih => rw [sum_range_succ,← ih,h]

private theorem column_span (k i : ℕ) (hi : i ≤ k) : BinSpan (3*k-i) (coeff k i) := by
  induction k generalizing i with
  | zero =>
    obtain rfl : i = 0 := by omega
    have e : coeff 0 0 = fun _ => 1 := by funext n; simp [coeff,diagonal_empty]
    rw [e]
    simpa using BinSpan.term (d := 0) 1 0 (by omega)
  | succ k ih =>
    have atZero (s : ℕ) : coeff (k+1) s 0 = 0 := by simp [coeff,diagonal_no_letters]
    cases i with
    | zero =>
      have e := prefix_of_step (f := coeff (k+1) 0) (g := fun n => n*(n*coeff k 0 n))
        (atZero _) (by simp) (coeff_step_zero k)
      rw [e]
      exact bin_mono (prefix_span (times_index (times_index (ih 0 (Nat.zero_le _))))) (by omega)
    | succ i =>
      have e := prefix_of_step (f := coeff (k+1) (i+1))
        (g := fun n => n*(n*coeff k (i+1) n) + n*coeff k i n)
        (atZero _) (by simp) (fun n => by rw [coeff_step_succ]; omega)
      have ri := times_index (ih i (by omega))
      have le : BinSpan (3*k-i+1) (fun n => n*(n*coeff k (i+1) n)) := by
        by_cases h : i+1 ≤ k
        · exact bin_mono (times_index (times_index (ih (i+1) h))) (by omega)
        · have hlt : k < i+1 := by omega
          have z (n : ℕ) : coeff k (i+1) n = 0 := Nat.le_zero.mp
            ((coeff_upper k (i+1) n).trans_eq (by simp [Nat.choose_eq_zero_of_lt hlt]))
          simpa [z] using bin_zero (3*k-i+1)
      rw [e]
      exact bin_mono (prefix_span (BinSpan.add le ri)) (by omega)

private theorem choose_hasSum (j : ℕ) {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n : ℕ => (n.choose j : ℝ)*t^n) (t^j/(1-t)^(j+1)) := by
  apply (hasSum_nat_add_iff' j).mp
  have zero : (∑ n ∈ range j, (n.choose j : ℝ)*t^n) = 0 := by
    apply sum_eq_zero
    intro n hn
    simp [Nat.choose_eq_zero_of_lt (mem_range.mp hn)]
  rw [zero,sub_zero]
  convert (hasSum_choose_mul_geometric_of_norm_lt_one j (by simpa only [Real.norm_eq_abs] using ht)).mul_right
    (t^j) using 1
  · funext n
    simp only [pow_add,mul_assoc]
  · ring

private theorem bin_polynomial {d : ℕ} {f : ℕ → ℕ} (h : BinSpan d f) :
    ∃ P : ℝ[X], ∀ t : ℝ, |t| < 1 →
      HasSum (fun n : ℕ => (f n : ℝ)*t^n) (P.eval t/(1-t)^(d+1)) := by
  induction h with
  | term a j hj =>
    refine ⟨C (a:ℝ)*X^j*(1-X)^(d-j),?_⟩
    intro t ht
    have hz : 1-t ≠ 0 := by have := (abs_lt.mp ht).2; linarith
    convert (choose_hasSum j ht).mul_left (a:ℝ) using 1
    · funext n
      simp only [Nat.cast_mul,mul_assoc]
    · simp only [eval_mul,eval_C,eval_pow,eval_X,eval_sub,eval_one]
      rw [show d+1=(d-j)+(j+1) by omega,pow_add]
      field_simp [hz]
  | add _ _ ih jh =>
    obtain ⟨P,hP⟩ := ih
    obtain ⟨Q,hQ⟩ := jh
    refine ⟨P+Q,?_⟩
    intro t ht
    convert (hP t ht).add (hQ t ht) using 1
    · funext n
      simp only [Nat.cast_add,add_mul]
    · simp only [eval_add,add_div]

/-- The polynomial determined by the defining generating series of GLZ, equation (2.6). -/
def sourcePolynomial (k i : ℕ) (hi : i ≤ k) : ℝ[X] :=
  (bin_polynomial (column_span k i hi)).choose

theorem sourcePolynomial_hasSum (k i : ℕ) (hi : i ≤ k) {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n : ℕ => (coeff k i n : ℝ)*t^n)
      ((sourcePolynomial k i hi).eval t / (1-t)^(3*k-i+1)) :=
  (bin_polynomial (column_span k i hi)).choose_spec t ht

theorem sourcePolynomial_eval (k i : ℕ) (hi : i ≤ k) {t : ℝ} (ht : |t| < 1) :
    (sourcePolynomial k i hi).eval t = numerator k i t := by
  rw [numerator,(sourcePolynomial_hasSum k i hi ht).tsum_eq]
  have hz : 1-t ≠ 0 := by have := (abs_lt.mp ht).2; linarith
  field_simp [hz]

theorem sourcePolynomial_unique (k i : ℕ) (hi : i ≤ k) (P : ℝ[X])
    (h : ∀ t : ℝ, |t| < 1 → P.eval t = numerator k i t) : P = sourcePolynomial k i hi := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioo_infinite (show (-1:ℝ)<1 by norm_num)).mono
  intro t ht
  exact (h t (abs_lt.mpr ht)).trans (sourcePolynomial_eval k i hi (abs_lt.mpr ht)).symm

/-- Every deletion column eventually has J distinct polynomial roots in the open interval (-1,0). -/
theorem eventual_sourcePolynomial_roots (J : ℕ) : ∀ᶠ k : ℕ in atTop, ∀ i : ℕ, ∀ hi : i ≤ k,
    Nonempty (Fin J ↪ {x : ℝ // x ∈ Set.Ioo (-1) 0 ∧ (sourcePolynomial k i hi).IsRoot x}) := by
  filter_upwards [eventual_distinct_negative_roots J] with k h
  intro i hi
  obtain ⟨e⟩ := h i hi
  let embed (v : Fin J) : {x : ℝ // x ∈ Set.Ioo (-1) 0 ∧ (sourcePolynomial k i hi).IsRoot x} :=
    ⟨(e v).val,(e v).property.1,by
      have ht := (e v).property.1
      exact (sourcePolynomial_eval k i hi (abs_lt.mpr ⟨ht.1,by linarith only [ht.2]⟩)).trans (e v).property.2⟩
  refine ⟨⟨embed,?_⟩⟩
  intro a b eq
  apply e.injective
  apply Subtype.ext
  exact congrArg (fun w : {x : ℝ // x ∈ Set.Ioo (-1) 0 ∧ (sourcePolynomial k i hi).IsRoot x} => w.val) eq

end
end JacobiStirlingExtreme

/-- info: 'JacobiStirlingExtreme.eventual_sourcePolynomial_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms JacobiStirlingExtreme.eventual_sourcePolynomial_roots
