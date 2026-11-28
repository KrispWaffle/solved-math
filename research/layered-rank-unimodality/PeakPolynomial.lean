module

public import GreedyBoxes
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace LayeredRanks
open Finset Polynomial
noncomputable section

def wordPoly (S : Finset (List ℕ)) : ℤ[X] := ∑ u ∈ S, X^u.sum
def rankPoly (w : List ℕ) : ℤ[X] := wordPoly (subwords w)

theorem rankPoly_coeff (w : List ℕ) (n : ℕ) :
    (rankPoly w).coeff n = (rankCount w n : ℤ) := by
  classical
  simp [rankPoly, wordPoly, rankCount, coeff_X_pow, Finset.sum_boole, eq_comm]

def firstAbove (b : ℕ) : List ℕ → Prop
  | [] => True
  | a::_ => b < a

instance (b : ℕ) (u : List ℕ) : Decidable (firstAbove b u) := by
  cases u <;> simp only [firstAbove] <;> infer_instance

def limited (b : ℕ) (w : List ℕ) := (subwords w).filter (firstAbove b)
def limitedPoly (b : ℕ) (w : List ℕ) := wordPoly (limited b w)
def letters (a b : ℕ) : ℤ[X] := ∑ t ∈ Icc (a+1) b, X^t

private theorem headStep (a c : ℕ) (u w : List ℕ) :
    Embeds (a::u) (c::w) ↔
      if 0<a ∧ a≤c then Embeds u w else Embeds (a::u) w := by
  simp only [← greedy_succeeds_iff, greedy]
  split <;> simp

theorem limited_zero (w : List ℕ) : limited 0 w = subwords w := by
  ext u
  simp only [limited, Finset.mem_filter, mem_subwords, and_iff_left_iff_imp]
  intro h
  obtain ⟨m, hm, _⟩ := (embeds_iff_unique_box _ _).1 h
  cases u with
  | nil => trivial
  | cons a v => exact ((inBox_iff _ _ _ _).1 hm).2 a v rfl

private theorem limited_step (b c : ℕ) (w : List ℕ) : limited b (c::w) =
    limited (max b c) w ∪ (Icc (b+1) c).biUnion
      (fun a => (subwords w).image (a :: ·)) := by
  ext u
  cases u with
  | nil => simp [limited, firstAbove, mem_subwords, show Embeds [] w from .nil,
                 show Embeds [] (c::w) from .nil]
  | cons a v =>
    simp [limited, firstAbove, mem_subwords, headStep, max_lt_iff]
    by_cases h : 0<a ∧ a≤c <;> simp [h] <;> grind

private theorem first_disjoint (b c : ℕ) (w : List ℕ) :
    Disjoint (limited (max b c) w) ((Icc (b+1) c).biUnion
      (fun a => (subwords w).image (a :: ·))) := by
  apply Finset.disjoint_left.2
  rintro u hu hu'
  obtain ⟨a, ha, ha'⟩ := Finset.mem_biUnion.1 hu'
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 ha'
  have highest : max b c < a := (Finset.mem_filter.1 hu).2
  have hac := (Finset.mem_Icc.1 ha).2
  omega

private theorem cons_disjoint (S : Finset (List ℕ)) (b c : ℕ) :
    ((Icc (b+1) c : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun a => S.image (a :: ·)) := by
  intro a _ a' _ he
  apply Finset.disjoint_left.2
  rintro u hu hv
  obtain ⟨_, _, rfl⟩ := Finset.mem_image.1 hu
  obtain ⟨_, _, hab⟩ := Finset.mem_image.1 hv
  exact he (List.cons.inj hab).1.symm

theorem limitedPoly_cons (b c : ℕ) (w : List ℕ) :
    limitedPoly b (c::w) = limitedPoly (max b c) w + letters b c * rankPoly w := by
  classical
  unfold limitedPoly rankPoly letters wordPoly
  rw [limited_step, Finset.sum_union (first_disjoint _ _ _),
    Finset.sum_biUnion (cons_disjoint _ _ _), Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_image, Finset.mul_sum]
  · apply Finset.sum_congr rfl
    intro v _
    simp [pow_add]
  · intro x _ y _ h
    exact (List.cons.inj h).2

private theorem nil_mem (w : List ℕ) : [] ∈ subwords w := mem_subwords.2 .nil

theorem limited_of_bound (b : ℕ) (w : List ℕ) (hw : ∀ a ∈ w, a ≤ b) :
    limited b w = {[]} := by
  induction w with
  | nil => simp [limited, subwords, firstAbove, Finset.filter_singleton]
  | cons c w ih =>
    have hc := hw c (by simp)
    rw [limited_step, max_eq_left hc, ih (fun a ha => hw a (by simp [ha]))]
    have emp : Icc (b+1) c = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    simp [emp]

@[simp] theorem rankPoly_nil : rankPoly [] = 1 := by simp [rankPoly, wordPoly, subwords]
@[simp] theorem limitedPoly_nil (b : ℕ) : limitedPoly b [] = 1 := by
  simp [limitedPoly, limited, wordPoly, subwords, Finset.filter_singleton, firstAbove]

theorem limitedPoly_zero (w : List ℕ) : limitedPoly 0 w = rankPoly w := by
  rw [limitedPoly, limited_zero, rankPoly]

theorem limitedPoly_of_bound (b : ℕ) (w : List ℕ) (hw : ∀ a ∈ w, a ≤ b) :
    limitedPoly b w = 1 := by simp [limitedPoly, limited_of_bound b w hw, wordPoly]

/-- Scanning before a maximum splits at the first letter that fails to extend the prefix. -/
theorem limitedPoly_peak (U V : List ℕ) (M b : ℕ) (hV : ∀ a ∈ V, a ≤ M) :
    limitedPoly b (U++M::V) =
      limitedPoly b U + (limitedPoly b (U++[M])-limitedPoly b U)*rankPoly V := by
  induction U generalizing b with
  | nil =>
    have hlim := limitedPoly_of_bound (max b M) V (fun a ha => (hV a ha).trans (le_max_right _ _))
    simp [limitedPoly_cons, hlim]
  | cons c U ih =>
    simp only [List.cons_append, limitedPoly_cons]
    rw [ih, ← limitedPoly_zero (U++M::V), ih]
    repeat rw [limitedPoly_zero]
    ring

private theorem reverse_embeds {u w : List ℕ} (h : Embeds u w) : Embeds u.reverse w.reverse := by
  obtain ⟨l, hv, hl⟩ := List.sublistForall₂_iff.1 h
  exact List.sublistForall₂_iff.2 ⟨l.reverse, List.forall₂_reverse_iff.2 hv, hl.reverse⟩

theorem rankPoly_reverse (w : List ℕ) : rankPoly w.reverse = rankPoly w := by
  classical
  have he : subwords w.reverse = (subwords w).image List.reverse := by
    ext u
    constructor
    · intro h
      have hu := reverse_embeds (mem_subwords.1 h)
      exact Finset.mem_image.2 ⟨u.reverse, mem_subwords.2 (by simpa using hu), by simp⟩
    · intro h
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      exact mem_subwords.2 (reverse_embeds (mem_subwords.1 hv))
  unfold rankPoly wordPoly
  rw [he, Finset.sum_image]
  · simp
  · intro a _ b _ h
    simpa using congrArg List.reverse h

theorem rankPoly_append_max (U : List ℕ) (M : ℕ) (hU : ∀ a ∈ U, a ≤ M) :
    rankPoly (U++[M]) = 1+letters 0 M * rankPoly U := by
  rw [← rankPoly_reverse (U++[M])]
  simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
  rw [← limitedPoly_zero, limitedPoly_cons, Nat.zero_max,
    limitedPoly_of_bound M U.reverse (by simpa using hU), rankPoly_reverse]

theorem rankPoly_peak (U V : List ℕ) (M : ℕ) (hU : ∀ a ∈ U, a ≤ M)
    (hV : ∀ a ∈ V, a ≤ M) : rankPoly (U++M::V) = rankPoly U + rankPoly V +
      (letters 0 M-1)*rankPoly U*rankPoly V := by
  have h := limitedPoly_peak U V M 0 hV
  simp only [limitedPoly_zero, rankPoly_append_max U M hU] at h
  rw [h]
  ring

/-- Concatenation of exactly n copies of a fixed finite composition. -/
def copies (v : List ℕ) : ℕ → List ℕ
  | 0 => []
  | n+1 => v ++ copies v n

def exitPoly (M : ℕ) (w : List ℕ) : ℤ[X] := 1+(letters 0 M-1)*rankPoly w

theorem exitPoly_peak (U V : List ℕ) (M : ℕ) (hU : ∀ a ∈ U, a ≤ M)
    (hV : ∀ a ∈ V, a ≤ M) : exitPoly M (U++M::V) = exitPoly M U * exitPoly M V := by
  simp only [exitPoly, rankPoly_peak U V M hU hV]
  ring

private theorem append_bound {U V : List ℕ} {M : ℕ} (hU : ∀ a ∈ U, a ≤ M)
    (hV : ∀ a ∈ V, a ≤ M) : ∀ a ∈ U++V, a ≤ M :=
  fun a ha => (List.mem_append.1 ha).elim (hU a) (hV a)

private theorem copies_bound {M : ℕ} (v : List ℕ) (hv : ∀ a ∈ v, a ≤ M) (n : ℕ) :
    ∀ a ∈ copies v n, a ≤ M := by
  induction n with
  | zero => simp [copies]
  | succ n ih =>
    intro a ha
    rcases List.mem_append.1 ha with h | h
    · exact hv a h
    · exact ih a h

private theorem cyclic_exit (U V : List ℕ) (M : ℕ) (hU : ∀ a ∈ U, a ≤ M)
    (hV : ∀ a ∈ V, a ≤ M) (n : ℕ) :
    exitPoly M (V ++ copies (U++M::V) n) = (exitPoly M (V++U))^n * exitPoly M V := by
  have hv : ∀ a ∈ U++M::V, a ≤ M := by
    intro a ha
    simp only [List.mem_append, List.mem_cons] at ha
    rcases ha with h | rfl | h
    · exact hU a h
    · rfl
    · exact hV a h
  induction n with
  | zero => simp [copies]
  | succ n ih =>
    have form : V ++ copies (U++M::V) (n+1) = (V++U) ++ M :: (V ++ copies (U++M::V) n) := by
      simp [copies, List.append_assoc]
    have hl : ∀ a ∈ V++U, a ≤ M := append_bound hV hU
    have hr : ∀ a ∈ V++copies (U++M::V) n, a ≤ M := append_bound hV (copies_bound _ hv n)
    rw [form, exitPoly_peak _ _ M hl hr, ih, pow_succ]
    ring

theorem periodic_exit (U V : List ℕ) (M : ℕ) (hU : ∀ a ∈ U, a ≤ M)
    (hV : ∀ a ∈ V, a ≤ M) (n : ℕ) :
    exitPoly M (copies (U++M::V) (n+1)) =
      (exitPoly M (V++U))^n * exitPoly M (U++M::V) := by
  have hv : ∀ a ∈ U++M::V, a ≤ M := by
    intro a ha
    simp only [List.mem_append, List.mem_cons] at ha
    rcases ha with h | rfl | h
    · exact hU a h
    · rfl
    · exact hV a h
  have hr : ∀ a ∈ V++copies (U++M::V) n, a ≤ M := append_bound hV (copies_bound _ hv n)
  rw [copies, List.append_assoc, List.cons_append, exitPoly_peak _ _ M hU hr,
    cyclic_exit _ _ M hU hV, exitPoly_peak _ _ M hU hV]
  ring

private theorem letters_sub_one_ne (M : ℕ) : letters 0 M - 1 ≠ 0 := by
  have hc : (letters 0 M).coeff 0 = 0 := by
    unfold letters
    rw [finsetSum_coeff]
    apply sum_eq_zero
    intro t ht
    have h := (Finset.mem_Icc.1 ht).1
    simp [coeff_X_pow, show 0 ≠ t by omega]
  intro h
  have e := congrArg (fun p : ℤ[X] => p.coeff 0) (sub_eq_zero.1 h)
  simp [hc] at e

/-- The geometric recurrence applies to the literal generating polynomial of
distinct words for any period split at a maximum. -/
theorem periodic_recurrence (U V : List ℕ) (M : ℕ) (hU : ∀ a ∈ U, a ≤ M)
    (hV : ∀ a ∈ V, a ≤ M) (n : ℕ) :
    rankPoly (copies (U++M::V) (n+2)) =
      rankPoly (V++U) + exitPoly M (V++U)*rankPoly (copies (U++M::V) (n+1)) := by
  have h1 := periodic_exit U V M hU hV (n+1)
  have h0 := periodic_exit U V M hU hV n
  apply mul_left_cancel₀ (letters_sub_one_ne M)
  simp only [exitPoly, pow_succ] at h1 h0 ⊢
  linear_combination h1 - (1+(letters 0 M-1)*rankPoly (V++U))*h0

theorem periodic_geometric_sum (U V : List ℕ) (M : ℕ) (hU : ∀ a ∈ U, a ≤ M)
    (hV : ∀ a ∈ V, a ≤ M) (n : ℕ) :
    rankPoly (copies (U++M::V) (n+1)) =
      rankPoly (V++U)*(∑ j ∈ range n, exitPoly M (V++U)^j) +
        rankPoly (U++M::V)*exitPoly M (V++U)^n := by
  induction n with
  | zero => simp [copies]
  | succ n ih =>
    rw [periodic_recurrence U V M hU hV, ih, sum_range_succ', pow_succ]
    simp only [pow_succ, ← sum_mul]
    ring

end
end LayeredRanks
