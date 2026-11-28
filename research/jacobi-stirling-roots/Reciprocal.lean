import SourcePolynomial
import Mathlib.RingTheory.Polynomial.Pochhammer

namespace JacobiStirlingExtreme

open Polynomial Finset
noncomputable section

private structure Presentation (d : ℕ) (f : ℕ → ℕ) where
  values : ℝ[X]
  num : ℝ[X]
  nat_eval (n : ℕ) : values.eval (n:ℝ) = (f n : ℝ)
  forward {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n : ℕ => (f n : ℝ)*t^n) (num.eval t/(1-t)^(d+1))
  backward {t : ℝ} (ht : |t| < 1) (hn : t ≠ 0) :
    HasSum (fun n : ℕ => values.eval (-((n:ℝ)+1))*t^n)
      ((-t)^d * num.eval t⁻¹/(1-t)^(d+1))

private theorem neg_choose (n j : ℕ) :
    (descPochhammer ℝ j).eval (-((n:ℝ)+1)) / j.factorial =
    (-1:ℝ)^j * ((n+j).choose j : ℝ) := by
  rw [Nat.cast_choose_eq_descPochhammer_div, Nat.cast_add,
    descPochhammer_eval_eq_ascPochhammer ℝ (-((n:ℝ)+1)) j,
    show -((n:ℝ)+1)-j+1 = -(n+j) by ring,ascPochhammer_eval_neg_eq_descPochhammer]
  ring

private theorem presentation_exists {d : ℕ} {f : ℕ → ℕ} (hf : BinSpan d f) :
    Nonempty (Presentation d f) := by
  induction hf with
  | term a j hj =>
    let V : ℝ[X] := C ((a:ℝ) / j.factorial) * descPochhammer ℝ j
    let P : ℝ[X] := C (a:ℝ)*X^j*(1-X)^(d-j)
    refine ⟨⟨V,P,?_,?_,?_⟩⟩
    · intro n
      simp only [V,eval_mul,eval_C,Nat.cast_mul,Nat.cast_choose_eq_descPochhammer_div]
      ring
    · intro t ht
      have hz : 1-t ≠ 0 := by have := (abs_lt.mp ht).2; linarith
      convert (choose_hasSum j ht).mul_left (a:ℝ) using 1
      · funext n
        simp [mul_assoc]
      · simp only [P,eval_mul,eval_C,eval_pow,eval_X,eval_sub,eval_one]
        rw [show d+1=(d-j)+(j+1) by omega,pow_add]
        field_simp [hz]
    · intro t ht hn
      have hz : 1-t ≠ 0 := by have := (abs_lt.mp ht).2; linarith
      have hprod : (-t)^d * (t⁻¹)^j * (1-t⁻¹)^(d-j) = (-1:ℝ)^j*(1-t)^(d-j) := by
        calc
          _ = ((-t)*t⁻¹)^j * ((-t)*(1-t⁻¹))^(d-j) := by
            have split : (-t)^d = (-t)^j * (-t)^(d-j) := by
              rw [← pow_add,Nat.add_sub_of_le hj]
            rw [split,mul_pow,mul_pow]
            ring
          _ = _ := by rw [show (-t)*t⁻¹ = -1 by field_simp,
                            show (-t)*(1-t⁻¹) = 1-t by field_simp; ring]
      convert (hasSum_choose_mul_geometric_of_norm_lt_one j
        (by simpa only [Real.norm_eq_abs] using ht)).mul_left ((a:ℝ)*(-1)^j) using 1
      · funext n
        simp only [V,eval_mul,eval_C]
        rw [show (a:ℝ)/j.factorial*(descPochhammer ℝ j).eval (-((n:ℝ)+1)) =
          a*((descPochhammer ℝ j).eval (-((n:ℝ)+1))/j.factorial) by ring,neg_choose]
        ring
      · simp only [P,eval_mul,eval_C,eval_pow,eval_X,eval_sub,eval_one]
        rw [show (-t)^d * (a*(t⁻¹)^j*(1-t⁻¹)^(d-j)) =
          a*((-t)^d*(t⁻¹)^j*(1-t⁻¹)^(d-j)) by ring,hprod,
          show d+1=(d-j)+(j+1) by omega,pow_add]
        field_simp [hz]
  | add _ _ ih jh =>
    obtain ⟨u⟩ := ih
    obtain ⟨v⟩ := jh
    refine ⟨⟨u.values+v.values,u.num+v.num,?_,?_,?_⟩⟩
    · intro n
      simp [u.nat_eval,v.nat_eval]
    · intro t ht
      convert (u.forward ht).add (v.forward ht) using 1
      · funext n
        simp [add_mul]
      · simp [add_div]
    · intro t ht hn
      convert (u.backward ht hn).add (v.backward ht hn) using 1
      · funext n
        simp [add_mul]
      · simp [mul_add,add_div]

private def sourcePresentation (k i : ℕ) (hi : i ≤ k) :=
  (presentation_exists (column_span k i hi)).some

/-- Polynomial in the diagonal index n with the exact source values at all natural n. -/
def sequencePolynomial (k i : ℕ) : ℝ[X] :=
  if hi : i ≤ k then (sourcePresentation k i hi).values else 0

theorem sequencePolynomial_nat (k i n : ℕ) : (sequencePolynomial k i).eval (n:ℝ) = (coeff k i n : ℝ) := by
  by_cases hi : i ≤ k
  · simpa [sequencePolynomial,hi] using (sourcePresentation k i hi).nat_eval n
  · have z : coeff k i n ≤ 0 := (coeff_upper k i n).trans_eq (by simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hi)])
    simp [sequencePolynomial,hi,Nat.le_zero.mp z]

private theorem eq_from_naturals {P Q : ℝ[X]} (h : ∀ n : ℕ, P.eval (n:ℝ) = Q.eval (n:ℝ)) : P=Q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R:=ℝ))).mono
  rintro _ ⟨n,rfl⟩
  exact h n

theorem sequencePolynomial_backward (k i : ℕ) (hi : i≤k) {t : ℝ} (ht : |t|<1) (hn : t≠0) :
    HasSum (fun n : ℕ => (sequencePolynomial k i).eval (-((n:ℝ)+1))*t^n)
      ((-t)^(3*k-i)*(sourcePolynomial k i hi).eval t⁻¹/(1-t)^(3*k-i+1)) := by
  let s := sourcePresentation k i hi
  have eq : s.num = sourcePolynomial k i hi := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.Ioo_infinite (show (-1:ℝ)<1 by norm_num)).mono
    intro x hx
    have h := (s.forward (abs_lt.mpr hx)).unique (sourcePolynomial_hasSum k i hi (abs_lt.mpr hx))
    have hz : 1-x ≠ 0 := by linarith only [hx.2]
    exact (div_left_inj₀ (pow_ne_zero _ hz)).mp h
  simpa only [sequencePolynomial,dite_eq_left hi,←eq] using s.backward ht hn

private theorem polynomial_step_zero (k : ℕ) (x : ℝ) :
    (sequencePolynomial (k+1) 0).eval (x-1) =
    (sequencePolynomial (k+1) 0).eval x - x*(x*(sequencePolynomial k 0).eval x) := by
  let P := sequencePolynomial (k+1) 0
  let Q := sequencePolynomial k 0
  have eq : P.comp (X+1) = P+(X+1)*((X+1)*Q.comp (X+1)) := by
    apply eq_from_naturals
    intro n
    simp only [P,Q,eval_comp,eval_add,eval_X,eval_one,eval_mul,
      ← Nat.cast_add_one,sequencePolynomial_nat,← Nat.cast_mul,← Nat.cast_add,coeff_step_zero]
  have e := congrArg (eval (x-1)) eq
  simp only [P,Q,eval_comp,eval_add,eval_X,eval_one,eval_mul,sub_add_cancel] at e
  linarith only [e]

private theorem polynomial_step_succ (k i : ℕ) (x : ℝ) :
    (sequencePolynomial (k+1) (i+1)).eval (x-1) =
    (sequencePolynomial (k+1) (i+1)).eval x - x*(x*(sequencePolynomial k (i+1)).eval x)
    - x*(sequencePolynomial k i).eval x := by
  let P := sequencePolynomial (k+1) (i+1)
  let Q := sequencePolynomial k (i+1)
  let U := sequencePolynomial k i
  have eq : P.comp (X+1) = P+(X+1)*((X+1)*Q.comp (X+1))+(X+1)*U.comp (X+1) := by
    apply eq_from_naturals
    intro n
    simp only [P,Q,U,eval_comp,eval_add,eval_X,eval_one,eval_mul,
      ← Nat.cast_add_one,sequencePolynomial_nat,← Nat.cast_mul,← Nat.cast_add,coeff_step_succ]
  have e := congrArg (eval (x-1)) eq
  simp only [P,Q,U,eval_comp,eval_add,eval_X,eval_one,eval_mul,sub_add_cancel] at e
  linarith only [e]

private def elementaryProduct (n : ℕ) : (ℕ[X])[X] :=
  ∏ j ∈ range n, (1 + C (letter (j+1)) * X)

/-- The k-th elementary symmetric polynomial of the first n Jacobi–Stirling letters. -/
def elementary (k n : ℕ) : ℕ[X] := (elementaryProduct n).coeff k

private theorem elementary_step (k n : ℕ) : elementary (k+1) (n+1) =
    elementary (k+1) n + letter (n+1)*elementary k n := by
  simp only [elementary,elementaryProduct,prod_range_succ,mul_add,mul_one,
    ←mul_assoc,coeff_add,coeff_mul_X,coeff_mul_C]
  ring

private theorem elementary_degree_zero (n : ℕ) : elementary 0 n = 1 := by
  induction n with
  | zero => simp [elementary,elementaryProduct]
  | succ n ih =>
    simpa only [elementary,elementaryProduct,prod_range_succ,mul_add,mul_one,
      ←mul_assoc,coeff_add,coeff_mul_X_zero,add_zero] using ih

private theorem sequence_zero_eval (k i : ℕ) :
    (sequencePolynomial k i).eval 0 = (coeff k i 0 : ℝ) := by
  simpa only [Nat.cast_zero] using sequencePolynomial_nat k i 0

private theorem letter_coeff_succ (m i : ℕ) (P : ℕ[X]) : (letter m * P).coeff (i+1) =
    m*(m*P.coeff (i+1))+m*P.coeff i := by
  simp [letter,mul_assoc,add_mul,mul_add]
  ring

private theorem empty_sequence (i : ℕ) :
    sequencePolynomial 0 i = C ((1 : ℕ[X]).coeff i : ℝ) := by
  apply eq_from_naturals
  intro n
  simp [sequencePolynomial_nat,coeff,diagonal_empty]

/-- At each negative integer the source sequence polynomial is the signed elementary symmetric
coefficient, with the same deletion index as at positive integers. -/
theorem negative_sequence_elementary (n k i : ℕ) :
    (sequencePolynomial k i).eval (-((n:ℝ)+1)) =
      (-1:ℝ)^k * (-1:ℝ)^i * ((elementary k n).coeff i : ℝ) := by
  induction n generalizing k i with
  | zero =>
    cases k with
    | zero =>
      cases i <;> simp [empty_sequence,elementary,elementaryProduct,Polynomial.coeff_one]
    | succ k =>
      cases i with
      | zero =>
        have e := polynomial_step_zero k 0
        simp only [zero_sub,zero_mul,sub_zero,sequence_zero_eval] at e
        simpa [coeff,diagonal_no_letters,elementary,elementaryProduct,Polynomial.coeff_one] using e
      | succ i =>
        have e := polynomial_step_succ k i 0
        simp only [zero_sub,zero_mul,sub_zero,sequence_zero_eval] at e
        simpa [coeff,diagonal_no_letters,elementary,elementaryProduct,Polynomial.coeff_one] using e
  | succ n ih =>
    cases k with
    | zero =>
      cases i <;> simp [empty_sequence,elementary_degree_zero,Polynomial.coeff_one]
    | succ k =>
      have xeq : -(((n+1:ℕ):ℝ)+1) = -((n:ℝ)+1)-1 := by push_cast; ring
      cases i with
      | zero =>
        rw [xeq,polynomial_step_zero,ih,ih,elementary_step]
        simp [letter,pow_succ,mul_add,add_mul]
        ring
      | succ i =>
        rw [xeq,polynomial_step_succ,ih,ih,ih,elementary_step,coeff_add,letter_coeff_succ]
        push_cast
        simp only [pow_succ]
        ring

private theorem signed_reciprocal_hasSum (k i : ℕ) (hi : i≤k) {t : ℝ} (ht : |t|<1) (hn : t≠0) :
    HasSum (fun n : ℕ => ((elementary k n).coeff i : ℝ)*t^n)
      (((-1:ℝ)^k*(-1:ℝ)^i)*(-t)^(3*k-i)*(sourcePolynomial k i hi).eval t⁻¹/(1-t)^(3*k-i+1)) := by
  have h := (sequencePolynomial_backward k i hi ht hn).mul_left ((-1:ℝ)^k*(-1:ℝ)^i)
  have one (j : ℕ) : (-1:ℝ)^j*(-1:ℝ)^j=1 := by rw [←mul_pow]; norm_num
  have pairs : ((-1:ℝ)^k*(-1)^i)*((-1)^k*(-1)^i)=1 := by
    calc
      _ = ((-1:ℝ)^k*(-1)^k)*((-1)^i*(-1)^i) := by ring
      _ = _ := by rw [one k,one i,one_mul]
  convert h using 1
  · funext n
    rw [negative_sequence_elementary]
    simp only [←mul_assoc,pairs,one_mul]
  · ring

private theorem elementary_zero_of_lt {n k : ℕ} (hk : n<k) : elementary k n=0 := by
  induction n generalizing k with
  | zero => simp [elementary,elementaryProduct,Polynomial.coeff_one,Nat.ne_of_gt hk]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k => rw [elementary_step,ih (by omega),ih (by omega),mul_zero,add_zero]

/-- The reversed numerator of the source conjecture, with exact denominator and deletion index,
generates the elementary-symmetric coefficients on alphabets of size k+s. -/
theorem elementary_reciprocal_hasSum (k i : ℕ) (hi : i≤k) {t : ℝ} (ht : |t|<1) (hn : t≠0) :
    HasSum (fun s : ℕ => ((elementary k (k+s)).coeff i : ℝ)*t^s)
      (t^(2*k-i)*(sourcePolynomial k i hi).eval t⁻¹/(1-t)^(3*k-i+1)) := by
  have parity : (-1:ℝ)^k*(-1)^i*(-1)^(3*k-i)=1 := by
    rw [←pow_add,←pow_add,show k+i+(3*k-i)=2*(2*k) by omega,pow_mul]
    norm_num
  have signedPower : (-1:ℝ)^k*(-1)^i*(-t)^(3*k-i)=t^(3*k-i) := by
    rw [show -t=(-1)*t by ring,mul_pow,←mul_assoc,parity,one_mul]
  have h := (hasSum_nat_add_iff' k).mpr (signed_reciprocal_hasSum k i hi ht hn)
  have z : (∑ n ∈ range k, ((elementary k n).coeff i : ℝ)*t^n)=0 := by
    apply sum_eq_zero
    intro n nh
    simp [elementary_zero_of_lt (mem_range.mp nh)]
  rw [signedPower,z,sub_zero] at h
  have split : t^(3*k-i) = t^(2*k-i)*t^k := by rw [←pow_add]; congr 1; omega
  convert h.mul_right (t^k)⁻¹ using 1
  · funext s
    rw [Nat.add_comm s k,pow_add]
    field_simp [hn]
  · rw [split]
    field_simp [hn]

end
end JacobiStirlingExtreme

/-- info: 'JacobiStirlingExtreme.elementary_reciprocal_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms JacobiStirlingExtreme.elementary_reciprocal_hasSum
