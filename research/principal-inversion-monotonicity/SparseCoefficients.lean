import UpperEdge
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Positivity

namespace PrincipalInversionMonotonicity

open StableInversions (invCount)

def digits : List Nat → List Nat
  | [] => []
  | a :: w => w.countP (· < a) :: digits w

@[simp] theorem length_digits (w : List Nat) : (digits w).length = w.length := by
  induction w <;> simp [digits, *]

@[simp] theorem sum_digits (w : List Nat) : (digits w).sum = invCount w := by
  induction w <;> simp [digits, invCount, *]

private theorem strict_head_rank {a b : Nat} (w : List Nat) (h : a < b) :
    (a :: w).countP (· < a) < (a :: w).countP (· < b) := by
  have le : w.countP (· < a) ≤ w.countP (· < b) :=
    List.countP_mono_left (by
      intro c _ hc
      exact decide_eq_true (Nat.lt_trans (of_decide_eq_true hc) h))
  simp [h]
  omega

theorem digits_injective_of_perm {u v : List Nat} (perm : u.Perm v) (e : digits u = digits v) :
    u = v := by
  induction u generalizing v with
  | nil => simpa using perm
  | cons a u ih =>
    cases v with
    | nil => simp at perm
    | cons b v =>
      obtain ⟨eqRank,eqTail⟩ := List.cons.inj e
      have ranks : (a :: u).countP (· < a) = (b :: v).countP (· < b) := by
        simpa using eqRank
      have headEq : a = b := by
        rcases lt_trichotomy a b with h | h | h
        · have lt := strict_head_rank u h
          rw [List.Perm.countP_eq (fun x => decide (x < b)) perm] at lt
          exact ((ne_of_lt lt) ranks).elim
        · exact h
        · have lt := strict_head_rank v h
          rw [List.Perm.countP_eq (fun x => decide (x < a)) perm.symm] at lt
          exact ((ne_of_lt lt) ranks.symm).elim
      subst b
      exact congrArg (List.cons a) (ih perm.cons_inv eqTail)

private def tagged : List (Nat × Fin 15) → List (Fin 16)
  | [] => []
  | (d,c) :: xs => List.replicate d 0 ++ c.succ :: tagged xs

private def readTags : List (Fin 16) → List (Nat × Fin 15)
  | [] => []
  | a :: w => Fin.cases
      (match readTags w with
       | [] => []
       | (d,c) :: xs => (d + 1,c) :: xs)
      (fun c => (0,c) :: readTags w) a

private theorem readRun (d : Nat) (c : Fin 15) (w : List (Fin 16)) :
    readTags (List.replicate d 0 ++ c.succ :: w) = (d,c) :: readTags w := by
  induction d with
  | zero => simp [readTags]
  | succ d ih => simp [List.replicate_succ, readTags, ih]

private theorem read_tagged (xs : List (Nat × Fin 15)) : readTags (tagged xs) = xs := by
  induction xs with
  | nil => rfl
  | cons p xs ih => rcases p with ⟨d,c⟩; simp [tagged, readRun, ih]

private theorem length_tagged (xs : List (Nat × Fin 15)) :
    (tagged xs).length = (xs.map Prod.fst).sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨d,c⟩
    simp [tagged, ih]
    omega

private def words (alphabet length : Nat) : Finset (List (Fin alphabet)) := by
  classical
  exact Finset.univ.image (List.ofFn : (Fin length → Fin alphabet) → _)

private theorem card_words (q n : Nat) : (words q n).card = q ^ n := by
  classical
  rw [words, Finset.card_image_of_injOn _]
  · simp
  · exact List.ofFn_injective.injOn

private theorem mem_words {q n : Nat} {w : List (Fin q)} :
    w ∈ words q n ↔ w.length = n := by
  classical
  constructor
  · intro hw
    obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hw
    simp
  · rintro rfl
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, List.ofFn_getElem⟩

/-- Exact counting inequality for every permutation family at one inversion weight.
There are fifteen independently chosen delimiters per digit and sixteen total symbols. -/
theorem coefficient_code_bound (D : List Nat → Prop) (n j : Nat) :
    (bucket D n j).card * 15 ^ n ≤ 16 ^ (n + j) := by
  classical
  rw [← card_words 15 n, ← card_words 16 (n + j), ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun p => tagged ((digits p.1).zip p.2))
  · rintro ⟨w,cs⟩ h
    obtain ⟨hw,hc⟩ := Finset.mem_product.mp h
    obtain ⟨perm, _, inv⟩ := mem_bucket.mp hw
    have lw : w.length = n := by simpa using perm.length_eq
    have lc := mem_words.mp hc
    apply mem_words.mpr
    rw [length_tagged, List.map_fst_zip (by simp [lw, lc])]
    simp [sum_digits, inv, lw, lc, Nat.add_comm]
  · rintro ⟨w,cs⟩ h ⟨w',cs'⟩ h' same
    obtain ⟨hw,hc⟩ := Finset.mem_product.mp h
    obtain ⟨hw',hc'⟩ := Finset.mem_product.mp h'
    have p := (mem_bucket.mp hw).1
    have p' := (mem_bucket.mp hw').1
    have l : (digits w).length = cs.length := by
      rw [length_digits, mem_words.mp hc]
      simpa using p.length_eq
    have l' : (digits w').length = cs'.length := by
      rw [length_digits, mem_words.mp hc']
      simpa using p'.length_eq
    have es := congrArg (fun z => (readTags z).unzip) same
    change (readTags (tagged ((digits w).zip cs))).unzip =
      (readTags (tagged ((digits w').zip cs'))).unzip at es
    rw [read_tagged, read_tagged, List.unzip_zip l, List.unzip_zip l'] at es
    obtain ⟨sameDigits, sameColors⟩ := Prod.mk.inj es
    exact Prod.ext (digits_injective_of_perm (p.trans p'.symm) sameDigits) sameColors

theorem coefficient_le_two_pow (D : List Nat → Prop) (n j exponent : Nat)
    (room : n + 32 * j ≤ 8 * exponent) : (bucket D n j).card ≤ 2 ^ exponent := by
  let b := (bucket D n j).card
  change b ≤ 2 ^ exponent
  apply (Nat.pow_le_pow_iff_left (n := 8) (by decide)).mp
  apply Nat.le_of_mul_le_mul_right (c := (15 ^ n) ^ 8) _ (by positivity)
  calc
    b ^ 8 * (15 ^ n) ^ 8 = (b * 15 ^ n) ^ 8 := (mul_pow ..).symm
    _ ≤ (16 ^ (n + j)) ^ 8 := Nat.pow_le_pow_left (coefficient_code_bound D n j) 8
    _ = (16 ^ 8) ^ n * 2 ^ (32 * j) := by
      rw [← pow_mul, show (n + j) * 8 = 8 * n + 8 * j by omega, pow_add, pow_mul]
      congr 1
      rw [show (16 : Nat) = 2 ^ 4 by decide, ← pow_mul]
      congr 1
      omega
    _ ≤ (2 * 15 ^ 8) ^ n * 2 ^ (32 * j) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide) n)
    _ = 2 ^ (n + 32 * j) * (15 ^ n) ^ 8 := by
      rw [mul_pow, pow_add, ← pow_mul, ← pow_mul, Nat.mul_comm 8 n]
      simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ ≤ (2 ^ exponent) ^ 8 * (15 ^ n) ^ 8 := by
      rw [← pow_mul (2 : Nat) exponent 8, Nat.mul_comm exponent 8]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide : 0 < 2) room)

end PrincipalInversionMonotonicity
