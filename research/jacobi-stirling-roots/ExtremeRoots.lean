import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace JacobiStirlingExtreme

open Polynomial Finset Filter
open scoped Topology
noncomputable section

/-- The Jacobi–Stirling alphabet has letters j(j+z). -/
def letter (j : ℕ) : ℕ[X] := C j * (X+C j)

/-- The complete homogeneous polynomial, enumerated by multiplicities of the n letters. -/
def diagonal (k n : ℕ) : ℕ[X] :=
  ∑ m : Fin n → Fin (k+1), if ∑ j, (m j : ℕ) = k then
    ∏ j, (letter (j.val+1))^(m j).val else 0

def coeff (k i n : ℕ) : ℕ := (diagonal k n).coeff i

def power (k i : ℕ) := k+(k-i)

private def LeCoeff (p q : ℕ[X]) := ∀ i, p.coeff i ≤ q.coeff i

private theorem mul_leCoeff {p q u v : ℕ[X]} (hp : LeCoeff p q) (hu : LeCoeff u v) :
    LeCoeff (p*u) (q*v) := by
  intro i
  simp only [coeff_mul]
  apply sum_le_sum
  intro j _
  exact Nat.mul_le_mul (hp _) (hu _)

private theorem pow_leCoeff {p q : ℕ[X]} (h : LeCoeff p q) (d : ℕ) :
    LeCoeff (p^d) (q^d) := by
  induction d with
  | zero => simp [LeCoeff]
  | succ d ih => simpa only [pow_succ] using mul_leCoeff ih h

private theorem prod_leCoeff {α : Type*} (s : Finset α) (f g : α → ℕ[X])
    (h : ∀ i ∈ s, LeCoeff (f i) (g i)) : LeCoeff (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [LeCoeff]
  | insert i s hi ih =>
    simp only [prod_insert hi]
    exact mul_leCoeff (h i (mem_insert_self ..)) (ih fun j hj => h j (mem_insert_of_mem hj))

private theorem letter_le {j n : ℕ} (h : j ≤ n) : LeCoeff (letter j) (letter n) := by
  intro i
  simp only [letter,coeff_C_mul,coeff_add,coeff_C]
  apply Nat.mul_le_mul h
  by_cases hi : i=0 <;> simp [hi,h]

theorem letter_power_coeff (n k i : ℕ) :
    ((letter n)^k).coeff i = k.choose i * n^(power k i) := by
  rw [letter,mul_pow,← C_pow,coeff_C_mul,coeff_X_add_C_pow]
  simp only [power,pow_add,Nat.cast_id]
  ac_rfl

theorem coeff_upper (k i n : ℕ) :
    coeff k i n ≤ (k+1)^n * (k.choose i * n^(power k i)) := by
  classical
  unfold coeff diagonal
  rw [finsetSum_coeff]
  have h (m : Fin n → Fin (k+1)) :
      (if ∑ j, (m j : ℕ) = k then ∏ j, (letter (j.val+1))^(m j).val else 0).coeff i ≤
        k.choose i * n^(power k i) := by
    split
    · rename_i size
      have hc := prod_leCoeff univ _ _ (fun (j : Fin n) _ =>
        pow_leCoeff (letter_le (show j.val+1 ≤ n from j.isLt)) (m j).val)
      have he : (∏ j, (letter n)^(m j).val) = (letter n)^k := by
        rw [prod_pow_eq_pow_sum,size]
      rw [← letter_power_coeff,← he]
      exact hc i
    · simp
  exact (sum_le_sum (fun m _ => h m)).trans_eq (by simp)

theorem coeff_lower (k i n : ℕ) :
    k.choose i * (n+1)^(power k i) ≤ coeff k i (n+1) := by
  classical
  let m : Fin (n+1) → Fin (k+1) := fun j => if j=Fin.last n then Fin.last k else 0
  have size : (∑ j, (m j : ℕ)) = k := by simp [m,apply_ite Fin.val]
  have he : (∏ j, (letter (j.val+1))^(m j).val) = (letter (n+1))^k := by
    simp [m,apply_ite Fin.val,pow_ite]
  unfold coeff diagonal
  rw [finsetSum_coeff]
  let f (m : Fin (n+1) → Fin (k+1)) := (if ∑ j, (m j : ℕ) = k then
    ∏ j, (letter (j.val+1))^(m j).val else 0).coeff i
  calc
    k.choose i * (n+1)^(power k i) = f m := by simp [f,size,he,letter_power_coeff]
    _ ≤ ∑ v, f v := single_le_sum (fun j _ => Nat.zero_le (f j)) (mem_univ m)

/-- With this rational base, n·base(j)^n is strictly largest at j. -/
def center (j : ℕ) : ℝ := (2*j-1)/(2*j+1)
def decay (j : ℕ) : ℝ := 1 - 1/((j : ℝ)*(2*j+1))
def peak (j n : ℕ) : ℝ := n * (center j)^n

private theorem parameters {j : ℕ} (hj : 0<j) :
    0 < center j ∧ center j < 1 ∧ 0 < decay j ∧ decay j < 1 ∧
    center j ≤ decay j ∧ decay j * center j ≤ 1 ∧
    ((j:ℝ)+1)*center j = (j:ℝ)*decay j ∧
    (j:ℝ)-1 ≤ (j:ℝ)*(decay j*center j) := by
  have h : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have a : (0:ℝ) < 2*j+1 := by positivity
  have b : (0:ℝ) < j*(2*j+1) := by positivity
  have vc : 0 < center j := by apply div_pos _ a; linarith
  have vu : center j < 1 := by unfold center; rw [div_lt_one a]; linarith
  have qc : 0 < decay j := by unfold decay; rw [sub_pos,div_lt_one b]; nlinarith
  have qu : decay j < 1 := by unfold decay; linarith [div_pos zero_lt_one b]
  have vq : center j ≤ decay j := by
    unfold center decay
    field_simp
    nlinarith
  refine ⟨vc,vu,qc,qu,vq,(mul_le_mul_of_nonneg_right qu.le vc.le).trans (by simpa using vu.le),?_,?_⟩
  · unfold center decay
    field_simp
    ring
  · have hj' : (0:ℝ)<j := by linarith
    unfold center decay
    field_simp
    nlinarith

private theorem peak_right_step {j n : ℕ} (hj : 0<j) (hn : j ≤ n) :
    peak j (n+1) ≤ decay j * peak j n := by
  obtain ⟨vc,_,_,_,vq,_,anchor,_⟩ := parameters hj
  have h : (j:ℝ) ≤ n := by exact_mod_cast hn
  have coef : ((n:ℝ)+1)*center j ≤ (n:ℝ)*decay j := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr vq)]
  unfold peak
  push_cast
  rw [pow_succ]
  nlinarith only [mul_nonneg (sub_nonneg.mpr coef) (pow_nonneg vc.le n)]

private theorem peak_left_step {j n : ℕ} (hj : 0<j) (hn : n<j) :
    peak j n ≤ decay j * peak j (n+1) := by
  obtain ⟨vc,_,_,_,_,vq,_,anchor⟩ := parameters hj
  have h : (n:ℝ)+1 ≤ j := by exact_mod_cast hn
  have coef : (n:ℝ) ≤ ((n:ℝ)+1)*(decay j*center j) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr vq)]
  unfold peak
  push_cast
  rw [pow_succ]
  nlinarith only [mul_nonneg (sub_nonneg.mpr coef) (pow_nonneg vc.le n)]

private theorem peak_right {j : ℕ} (hj : 0<j) (h : ℕ) :
    peak j (j+h) ≤ (decay j)^h * peak j j := by
  induction h with
  | zero => simp
  | succ h ih =>
    calc
      peak j (j+h+1) ≤ decay j * peak j (j+h) := peak_right_step hj (by omega)
      _ ≤ decay j * ((decay j)^h * peak j j) :=
        mul_le_mul_of_nonneg_left ih (parameters hj).2.2.1.le
      _ = _ := by rw [pow_succ]; ring

private theorem peak_left {j : ℕ} (hj : 0<j) (h : ℕ) (hh : h ≤ j) :
    peak j (j-h) ≤ (decay j)^h * peak j j := by
  induction h with
  | zero => simp
  | succ h ih =>
    have he : (j-(h+1))+1 = j-h := by omega
    calc
      peak j (j-(h+1)) ≤ decay j * peak j (j-(h+1)+1) := peak_left_step hj (by omega)
      _ ≤ decay j * ((decay j)^h * peak j j) := by
        rw [he]
        exact mul_le_mul_of_nonneg_left (ih (by omega)) (parameters hj).2.2.1.le
      _ = _ := by rw [pow_succ]; ring

def weight (k i j n : ℕ) : ℝ := (coeff k i n : ℝ) * ((center j)^(power k i))^n

private theorem weight_upper (k i j n : ℕ) (hj : 0<j) :
    weight k i j n ≤ (k+1 : ℕ)^n * (k.choose i : ℝ) * (peak j n)^(power k i) := by
  have hc : (coeff k i n : ℝ) ≤ ((k:ℝ)+1)^n * ((k.choose i : ℝ) * (n:ℝ)^power k i) := by
    exact_mod_cast coeff_upper k i n
  have h := mul_le_mul_of_nonneg_right hc (pow_nonneg (pow_nonneg (parameters hj).1.le (power k i)) n)
  unfold weight peak
  push_cast
  convert h using 1
  rw [mul_pow,← pow_mul,← pow_mul, Nat.mul_comm n (power k i)]
  ring

private theorem weight_lower (k i j : ℕ) (hj : 0<j) :
    (k.choose i : ℝ) * (peak j j)^(power k i) ≤ weight k i j j := by
  have hc : (k.choose i : ℝ) * (j:ℝ)^power k i ≤ coeff k i j := by
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    exact_mod_cast coeff_lower k i a
  unfold weight peak
  rw [mul_pow,← mul_assoc]
  convert mul_le_mul_of_nonneg_right hc (pow_nonneg (pow_nonneg (parameters hj).1.le _) j) using 1
  rw [← pow_mul,← pow_mul, Nat.mul_comm j (power k i)]

private theorem weight_off {k i j n h : ℕ} (hj : 0<j) (hn : n ≤ (j+1)*h)
    (hp : peak j n ≤ (decay j)^h * peak j j)
    (small : ((k:ℝ)+1)^(j+1) * (decay j)^k ≤ 1/4) :
    weight k i j n ≤ weight k i j j * (1/4 : ℝ)^h := by
  have pk (a : ℕ) : 0 ≤ peak j a := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (parameters hj).1.le _)
  have q0 := (parameters hj).2.2.1.le
  have q1 := (parameters hj).2.2.2.1.le
  have kD : k ≤ power k i := Nat.le_add_right _ _
  have hq := pow_le_pow_of_le_one q0 q1 kD
  have hnat : 1 ≤ (k:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  calc
    weight k i j n ≤ ((k:ℝ)+1)^n * (k.choose i : ℝ) * (peak j n)^(power k i) := by
      simpa using weight_upper k i j n hj
    _ ≤ ((k:ℝ)+1)^((j+1)*h) * (k.choose i : ℝ) *
        ((decay j)^h * peak j j)^(power k i) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hnat hn) (Nat.cast_nonneg _))
        (pow_le_pow_left₀ (pk _) hp _) (pow_nonneg (pk _) _) (by positivity)
    _ = ((k.choose i : ℝ) * (peak j j)^(power k i)) *
        (((k:ℝ)+1)^(j+1) * (decay j)^(power k i))^h := by
      have swap : ((decay j)^h)^(power k i) = ((decay j)^(power k i))^h := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [mul_pow,mul_pow,pow_mul,swap]
      ring
    _ ≤ weight k i j j * (1/4 : ℝ)^h := by
      apply mul_le_mul (weight_lower k i j hj) _
        (pow_nonneg (mul_nonneg (by positivity) (pow_nonneg q0 _)) _)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (pow_nonneg (parameters hj).1.le _) _))
      exact pow_le_pow_left₀ (mul_nonneg (by positivity) (pow_nonneg q0 _))
        ((mul_le_mul_of_nonneg_left hq (by positivity)).trans small) h

private theorem right_bound {k i j : ℕ} (hj : 0<j) (m : ℕ)
    (small : ((k:ℝ)+1)^(j+1)*(decay j)^k ≤ 1/4) :
    weight k i j (j+(m+1)) ≤ weight k i j j * (1/4 : ℝ)^(m+1) := by
  apply weight_off hj _ (peak_right hj (m+1)) small
  nlinarith only [Nat.zero_le (j*m)]

private theorem left_bound {k i j : ℕ} (hj : 0<j) {m : ℕ} (hm : m<j)
    (small : ((k:ℝ)+1)^(j+1)*(decay j)^k ≤ 1/4) :
    weight k i j (j-(m+1)) ≤ weight k i j j * (1/4 : ℝ)^(m+1) := by
  apply weight_off hj _ (peak_left hj (m+1) hm) small
  calc
    j-(m+1) ≤ j+1 := by omega
    _ ≤ (j+1)*(m+1) := Nat.le_mul_of_pos_right _ (by omega)

private theorem eventual_small {j : ℕ} (hj : 0<j) :
    ∀ᶠ k : ℕ in atTop, ((k:ℝ)+1)^(j+1)*(decay j)^k ≤ 1/4 := by
  have ht := tendsto_pow_const_mul_const_pow_of_lt_one (j+1)
    (parameters hj).2.2.1.le (parameters hj).2.2.2.1
  have cpos : 0 < (1/4 : ℝ)/2^(j+1) := by positivity
  filter_upwards [ht.eventually_lt_const cpos, eventually_ge_atTop 1] with k hk gone
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast gone
  have hpow : ((k:ℝ)+1)^(j+1) ≤ (2*(k:ℝ))^(j+1) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  calc
    _ ≤ (2*(k:ℝ))^(j+1)*(decay j)^k :=
      mul_le_mul_of_nonneg_right hpow (pow_nonneg (parameters hj).2.2.1.le k)
    _ = ((k:ℝ)^(j+1)*(decay j)^k)*2^(j+1) := by rw [mul_pow]; ring
    _ ≤ _ := (le_div_iff₀ (by positivity)).mp hk.le

/-- The evaluation of the source numerator via its ordinary generating function.
The arguments below use this formula only inside its disk of convergence. -/
def numerator (k i : ℕ) (t : ℝ) : ℝ :=
  (1-t)^(3*k-i+1) * ∑' n : ℕ, (coeff k i n : ℝ)*t^n

private theorem term_majorant {k i n : ℕ} {t R : ℝ} (ht : |t| ≤ R) :
    ‖(coeff k i n : ℝ)*t^n‖ ≤ (k.choose i : ℝ)*((n:ℝ)^power k i * (((k:ℝ)+1)*R)^n) := by
  have h : (coeff k i n : ℝ) ≤ ((k:ℝ)+1)^n * ((k.choose i : ℝ) * (n:ℝ)^power k i) := by
    exact_mod_cast coeff_upper k i n
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ (((k:ℝ)+1)^n * ((k.choose i : ℝ) * (n:ℝ)^power k i)) * R^n :=
      mul_le_mul h (pow_le_pow_left₀ (abs_nonneg _) ht _) (pow_nonneg (abs_nonneg _) _) (by positivity)
    _ = _ := by rw [mul_pow]; ring

private theorem majorant_summable (k i : ℕ) {R : ℝ} (hR : 0 ≤ R) (h : ((k:ℝ)+1)*R < 1) :
    Summable (fun n : ℕ => (k.choose i : ℝ)*((n:ℝ)^power k i * (((k:ℝ)+1)*R)^n)) := by
  apply Summable.mul_left
  apply summable_pow_mul_geometric_of_norm_lt_one
  rwa [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hR)]

private theorem numerator_continuousOn {k i : ℕ} {R : ℝ} (hR : 0 ≤ R) (h : ((k:ℝ)+1)*R < 1) :
    ContinuousOn (numerator k i) (Set.Icc (-R) R) := by
  unfold numerator
  have factor (d : ℕ) : Continuous (fun t : ℝ => (1-t)^d) := by fun_prop
  refine (factor (3*k-i+1)).continuousOn.mul ?_
  apply continuousOn_tsum (fun _ => by fun_prop) (majorant_summable k i hR h)
  intro n t ht
  exact term_majorant (abs_le.mpr ht)

private theorem small_radius {k i j : ℕ} (hj : 0<j)
    (small : ((k:ℝ)+1)^(j+1)*(decay j)^k ≤ 1/4) : ((k:ℝ)+1)*(center j)^power k i < 1 := by
  obtain ⟨vc,_,qc,qu,vq,_⟩ := parameters hj
  have hnat : 1 ≤ (k:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hbase : (k:ℝ)+1 ≤ ((k:ℝ)+1)^(j+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hnat (show 1 ≤ j+1 by omega)
  have hpow : (center j)^power k i ≤ (decay j)^k :=
    (pow_le_pow_left₀ vc.le vq _).trans
      (pow_le_pow_of_le_one qc.le qu.le (Nat.le_add_right k (k-i)))
  exact ((mul_le_mul hbase hpow (pow_nonneg vc.le _) (by positivity)).trans small).trans_lt (by norm_num)

private theorem central_error {f : ℕ → ℝ} {s W : ℝ} {j : ℕ} (hf : HasSum f s) (hW : 0 ≤ W)
    (left : ∀ m<j, |f (j-(m+1))| ≤ W*(1/4 : ℝ)^(m+1))
    (right : ∀ m, |f (j+(m+1))| ≤ W*(1/4 : ℝ)^(m+1)) : |s-f j| ≤ 2*W/3 := by
  let g (m : ℕ) := W*(1/4 : ℝ)^(m+1)
  have hg : HasSum g (W/3) := by
    convert (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num)).mul_left (W*(1/4)) using 1
    · funext m
      dsimp [g]
      rw [pow_succ]
      ring
    · ring
  have g0 (m : ℕ) : 0 ≤ g m := mul_nonneg hW (by positivity)
  have lower : |∑ n ∈ range j, f n| ≤ W/3 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [← Finset.sum_range_reflect (fun n => |f n|) j]
    calc
      _ ≤ ∑ m ∈ range j, g m := by
        apply sum_le_sum
        intro m hm
        rw [show j-1-m=j-(m+1) by omega]
        exact left m (mem_range.mp hm)
      _ ≤ _ := (hg.summable.sum_le_tsum _ (fun m _ => g0 m)).trans_eq hg.tsum_eq
  have rt (m : ℕ) : ‖f (m+(j+1))‖ ≤ g m := by
    rw [Real.norm_eq_abs, show m+(j+1) = j+(m+1) by omega]
    exact right m
  have hrt := Summable.of_nonneg_of_le (fun m => norm_nonneg (f (m+(j+1)))) rt hg.summable
  have upper : |∑' m, f (m+(j+1))| ≤ W/3 := by
    rw [← Real.norm_eq_abs]
    exact (norm_tsum_le_tsum_norm hrt).trans ((hrt.tsum_mono hg.summable rt).trans_eq hg.tsum_eq)
  have all := hf.summable.sum_add_tsum_nat_add (j+1)
  rw [sum_range_succ,hf.tsum_eq] at all
  rw [show s-f j = (∑ n ∈ range j, f n) + ∑' m, f (m+(j+1)) by linarith only [all]]
  exact (abs_add_le ..).trans (by linarith only [lower,upper])

private theorem point_sign {k i j : ℕ} (hi : i ≤ k) (hj : 0<j)
    (small : ((k:ℝ)+1)^(j+1)*(decay j)^k ≤ 1/4) :
    (Even j → 0 < numerator k i (-(center j^power k i))) ∧
    (Odd j → numerator k i (-(center j^power k i)) < 0) := by
  let R := center j ^ power k i
  let f (n : ℕ) := (coeff k i n : ℝ) * (-R)^n
  have hR : 0 < R := pow_pos (parameters hj).1 _
  have hs : Summable f := (majorant_summable k i hR.le (small_radius hj small)).of_norm_bounded
    (fun _ => term_majorant (by rw [abs_neg,abs_of_pos hR]))
  have aw (n : ℕ) : |f n| = weight k i j n := by
    simp only [f,weight,abs_mul,abs_pow,abs_neg,abs_of_pos hR,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (coeff k i n)),R]
  have hw : 0 < weight k i j j := by
    apply lt_of_lt_of_le _ (weight_lower k i j hj)
    apply mul_pos (by exact_mod_cast Nat.choose_pos hi)
    exact pow_pos (mul_pos (by exact_mod_cast hj) (pow_pos (parameters hj).1 _)) _
  have err := central_error hs.hasSum hw.le
    (fun m hm => (aw _).le.trans (left_bound hj hm small))
    (fun m => (aw _).le.trans (right_bound hj m small))
  obtain ⟨lo,up⟩ := abs_le.mp err
  have factor : 0 < (1-(-R))^(3*k-i+1) := pow_pos (by linarith only [hR]) _
  change (Even j → 0 < (1-(-R))^(3*k-i+1)*(∑' n, f n)) ∧
    (Odd j → (1-(-R))^(3*k-i+1)*(∑' n, f n) < 0)
  constructor
  · intro he
    have e : f j = weight k i j j := by simp only [f,he.neg_pow,weight,R]
    exact mul_pos factor (by linarith only [lo,e,hw])
  · intro ho
    have e : f j = -weight k i j j := by simp only [f,ho.neg_pow,mul_neg,weight,R]
    exact mul_neg_of_pos_of_neg factor (by linarith only [up,e,hw])

private theorem center_strictMono : StrictMono center := by
  intro a b hab
  have h : (a:ℝ) < b := by exact_mod_cast hab
  unfold center
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith only [h]

private theorem root_between {k i j : ℕ} (hk : 0 < k) (hi : i ≤ k) (hj : 0 < j)
    (small : ((k:ℝ)+1)^(j+1)*(decay j)^k ≤ 1/4)
    (next : ((k:ℝ)+1)^(j+1+1)*(decay (j+1))^k ≤ 1/4) :
    ∃ x ∈ Set.Ioo (-(center (j+1)^power k i)) (-(center j^power k i)), numerator k i x = 0 := by
  have hj' : 0<j+1 := by omega
  let a := center j ^ power k i
  let b := center (j+1) ^ power k i
  have ha : 0<a := pow_pos (parameters hj).1 _
  have hb : 0<b := pow_pos (parameters hj').1 _
  have hab : a < b := pow_lt_pow_left₀ (center_strictMono (Nat.lt_succ_self j))
    (parameters hj).1.le (show power k i ≠ 0 by unfold power; omega)
  have con : ContinuousOn (numerator k i) (Set.Icc (-b) (-a)) :=
    (numerator_continuousOn hb.le (small_radius hj' next)).mono
      (Set.Icc_subset_Icc le_rfl (by linarith only [ha,hb]))
  have sa := point_sign hi hj small
  have sb := point_sign hi hj' next
  rcases Nat.even_or_odd j with he | ho
  · exact intermediate_value_Ioo (neg_le_neg hab.le) con ⟨sb.2 he.add_one,sa.1 he⟩
  · exact intermediate_value_Ioo' (neg_le_neg hab.le) con ⟨sa.2 ho,sb.1 ho.add_one⟩

/-- Every deletion column eventually has a zero in each of the first J disjoint
negative intervals. The threshold depends only on J, including when i varies with k. -/
theorem eventual_roots_in_intervals (J : ℕ) : ∀ᶠ k : ℕ in atTop, ∀ i ≤ k, ∀ j ∈ Icc 1 J,
    ∃ x ∈ Set.Ioo (-(center (j+1)^power k i)) (-(center j^power k i)), numerator k i x = 0 := by
  have small : ∀ᶠ k : ℕ in atTop, ∀ j ∈ Icc 1 (J+1), ((k:ℝ)+1)^(j+1)*(decay j)^k ≤ 1/4 :=
    (Finset.eventually_all _).mpr (fun j hj => eventual_small (mem_Icc.mp hj).1)
  filter_upwards [small,eventually_ge_atTop 1] with k h hk
  intro i hi j hj
  obtain ⟨jpos,jle⟩ := mem_Icc.mp hj
  exact root_between hk hi jpos (h _ (mem_Icc.mpr ⟨jpos,by omega⟩))
    (h _ (mem_Icc.mpr ⟨by omega,by omega⟩))

/-- Uniformly over the whole row, the number of distinct negative zeros tends to infinity. -/
theorem eventual_distinct_negative_roots (J : ℕ) : ∀ᶠ k : ℕ in atTop, ∀ i ≤ k,
    Nonempty (Fin J ↪ {x : ℝ // x < 0 ∧ numerator k i x = 0}) := by
  classical
  filter_upwards [eventual_roots_in_intervals J] with k h
  intro i hi
  have each (m : Fin J) := h i hi (m.val+1) (mem_Icc.mpr ⟨by omega, m.isLt⟩)
  choose x hx hz using each
  have neg (m : Fin J) : x m < 0 := (hx m).2.trans (neg_lt_zero.mpr
    (pow_pos (parameters (Nat.zero_lt_succ m.val)).1 _))
  have decreasing {a b : Fin J} (hab : a<b) : x b < x a := by
    have h' : a.val+1+1 ≤ b.val+1 := by change a.val < b.val at hab; omega
    have hpow := pow_le_pow_left₀ (parameters (Nat.zero_lt_succ (a.val+1))).1.le
      (center_strictMono.monotone h') (power k i)
    exact (hx b).2.trans_le (neg_le_neg hpow) |>.trans (hx a).1
  refine ⟨⟨fun m => ⟨x m,neg m,hz m⟩,?_⟩⟩
  intro a b eq
  have e : x a=x b := congrArg Subtype.val eq
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact ((decreasing hlt).ne e.symm).elim
  · exact heq
  · exact ((decreasing hgt).ne e).elim

end
end JacobiStirlingExtreme

/-- info: 'JacobiStirlingExtreme.eventual_distinct_negative_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms JacobiStirlingExtreme.eventual_distinct_negative_roots
