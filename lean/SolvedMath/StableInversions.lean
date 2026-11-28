module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Permutation

@[expose] public section

namespace StableInversions

/-- The exact relative order of r increasing entries followed by a descent above them. -/
def shape : ℕ → List ℕ → Prop
  | 0, [a,b] => b < a
  | 0, _ => False
  | _+1, [] => False
  | r+1, a::v => (∀ b ∈ v, a < b) ∧ shape r v

def occurs (r : ℕ) (w : List ℕ) : Prop := ∃ v, shape r v ∧ v.Sublist w

private theorem occurs_mono (r : ℕ) {u w : List ℕ} (sub : u.Sublist w) : occurs r u → occurs r w :=
  fun ⟨v, hv, hs⟩ => ⟨v, hv, hs.trans sub⟩

private theorem insert_sublist (L R : List ℕ) : (L++R).Sublist (L++0::R) :=
  (List.Sublist.cons 0 (List.Sublist.refl R)).append_left L

private theorem remove_zero {v : List ℕ} (L R : List ℕ) (hz : 0 ∉ v)
    (h : v.Sublist (L++0::R)) : v.Sublist (L++R) := by
  induction L generalizing v with
  | nil =>
    cases h with
    | cons _ h => exact h
    | cons_cons _ _ => simp at hz
  | cons a L ih =>
    cases h with
    | cons _ h => exact .cons _ (ih hz h)
    | cons_cons _ h => exact .cons_cons _ (ih (fun e => hz (by simp [e])) h)

private theorem after_zero {v : List ℕ} (L R : List ℕ) (hL : 0 ∉ L) (hR : 0 ∉ R)
    (h : (0::v).Sublist (L++0::R)) : v.Sublist R := by
  induction L with
  | nil =>
    cases h with
    | cons _ h => exact (hR (h.subset (by simp))).elim
    | cons_cons _ h => exact h
  | cons a L ih =>
    cases h with
    | cons _ h => exact ih (fun e => hL (by simp [e])) h
    | cons_cons _ h => simp at hL

/-- A newly created occurrence using the inserted minimum starts there. -/
theorem occurs_succ_insert (r : ℕ) (L R : List ℕ) (hL : 0 ∉ L) (hR : 0 ∉ R) :
    occurs (r+1) (L++0::R) ↔ occurs (r+1) (L++R) ∨ occurs r R := by
  constructor
  · rintro ⟨v, hv, hs⟩
    by_cases hz : 0 ∈ v
    · cases v with
      | nil => simp at hz
      | cons a v =>
        have rules : (∀ b ∈ v, a < b) ∧ shape r v := hv
        have ha : a=0 := by
          rcases List.mem_cons.1 hz with h | h
          · exact h.symm
          · have := rules.1 _ h; omega
        subst a
        exact Or.inr ⟨v, rules.2, after_zero L R hL hR hs⟩
    · exact Or.inl ⟨v, hv, remove_zero L R hz hs⟩
  · rintro (old | ⟨v, hv, hs⟩)
    · exact occurs_mono _ (insert_sublist L R) old
    · refine ⟨0::v, ⟨?_, hv⟩, (List.Sublist.cons_cons 0 hs).trans (List.sublist_append_right _ _)⟩
      intro b hb
      have pos : b≠0 := fun e => hR (e ▸ hs.subset hb)
      omega

/-- Width of the initial segment of cuts whose remaining suffix contains the pattern. -/
noncomputable def cutoff (r : ℕ) : List ℕ → ℕ
  | [] => 0
  | a::w => by classical exact if occurs r (a::w) then cutoff r w+1 else 0

private theorem not_shape_nil (r : ℕ) : ¬ shape r [] := by cases r <;> simp [shape]

@[simp] theorem not_occurs_nil (r : ℕ) : ¬ occurs r [] := by
  rintro ⟨v, hv, hs⟩
  have := List.sublist_nil.1 hs
  subst v
  exact not_shape_nil _ hv

theorem occurs_drop_iff (r : ℕ) (w : List ℕ) (i : ℕ) :
    occurs r (w.drop i) ↔ i < cutoff r w := by
  classical
  induction w generalizing i with
  | nil => simp [cutoff]
  | cons a w ih =>
    by_cases h : occurs r (a::w)
    · cases i with
      | zero => simp [cutoff, h]
      | succ i => simpa [cutoff, h] using ih i
    · have hn : ¬ occurs r ((a::w).drop i) := fun e => h (occurs_mono _ (List.drop_sublist _ _) e)
      simp [cutoff, h, hn]

/-- Inserting a new minimum after i positions is legal for 1243 precisely at this cutoff. -/
theorem avoids1243_insert (L R : List ℕ) (hL : 0 ∉ L) (hR : 0 ∉ R)
    (avoids : ¬ occurs 2 (L++R)) : ¬ occurs 2 (L++0::R) ↔ cutoff 1 (L++R) ≤ L.length := by
  have tail := occurs_drop_iff 1 (L++R) L.length
  simp only [List.drop_left] at tail
  simp [occurs_succ_insert 1 L R hL hR, avoids, tail]

theorem occurs_zero_iff (w : List ℕ) : occurs 0 w ↔ ∃ a b, b<a ∧ [a,b].Sublist w := by
  constructor
  · rintro ⟨v, hv, hs⟩
    cases v with
    | nil => exact False.elim hv
    | cons a v => cases v with
      | nil => exact False.elim hv
      | cons b v => cases v with
        | nil => exact ⟨_, _, hv, hs⟩
        | cons c v => exact False.elim hv
  · rintro ⟨a,b,h,hs⟩; exact ⟨[a,b],h,hs⟩

private theorem occurs_zero_insert (L R : List ℕ) (hL : 0 ∉ L) :
    occurs 0 (L++0::R) ↔ occurs 0 (L++R) ∨ L≠[] := by
  cases L with
  | nil =>
    simp only [List.nil_append, ne_eq, not_true_eq_false, or_false]
    constructor
    · rw [occurs_zero_iff, occurs_zero_iff]
      rintro ⟨a,b,hab,hs⟩
      cases hs with
      | cons _ h => exact ⟨_,_,hab,h⟩
      | cons_cons _ _ => omega
    · exact occurs_mono _ (List.Sublist.cons 0 (List.Sublist.refl R))
  | cons a L =>
    have ha : 0<a := by have hn : a≠0 := fun e => hL (by simp [e]); omega
    have good : occurs 0 ((a::L)++0::R) := (occurs_zero_iff _).2
      ⟨a,0,ha,.cons_cons a (List.singleton_sublist.2 (by simp))⟩
    exact ⟨fun _ => Or.inr (by simp), fun _ => good⟩

private theorem drop_past (L R : List ℕ) (j : ℕ) (hj : L.length<j) :
    (L++0::R).drop j = (L++R).drop (j-1) := by
  have step : j-L.length = (j-1-L.length)+1 := by omega
  simp [List.drop_append, List.drop_eq_nil_of_le (show L.length≤j by omega),
    List.drop_eq_nil_of_le (show L.length≤j-1 by omega), step]

private theorem nat_lt_ext {x y : ℕ} (h : ∀ j, j<x ↔ j<y) : x=y := by
  have hx := h x
  have hy := h y
  omega

theorem cutoff_inversion_insert (L R : List ℕ) (hL : 0 ∉ L) :
    cutoff 0 (L++0::R) = if L.length < cutoff 0 (L++R) then cutoff 0 (L++R)+1 else L.length := by
  apply nat_lt_ext
  intro j
  rw [← occurs_drop_iff]
  by_cases hj : j ≤ L.length
  · rw [List.drop_append_of_le_length hj, occurs_zero_insert _ _ (fun e => hL ((List.drop_sublist _ _).subset e)),
      ← List.drop_append_of_le_length hj, occurs_drop_iff]
    simp only [ne_eq, List.drop_eq_nil_iff]
    split <;> omega
  · rw [drop_past _ _ _ (by omega), occurs_drop_iff]
    split <;> omega

theorem cutoff_132_insert (L R : List ℕ) (hL : 0 ∉ L) (hR : 0 ∉ R)
    (allowed : cutoff 1 (L++R) ≤ L.length) :
    cutoff 1 (L++0::R) = if L.length < cutoff 0 (L++R) then L.length+1 else cutoff 1 (L++R) := by
  apply nat_lt_ext
  intro j
  rw [← occurs_drop_iff]
  by_cases hj : j ≤ L.length
  · rw [List.drop_append_of_le_length hj, occurs_succ_insert 0 _ _ (fun e => hL ((List.drop_sublist _ _).subset e)) hR,
      ← List.drop_append_of_le_length hj, occurs_drop_iff]
    have right := occurs_drop_iff 0 (L++R) L.length
    rw [List.drop_left] at right
    rw [right]
    change (j < cutoff 1 (L++R) ∨ L.length < cutoff 0 (L++R)) ↔ _
    split <;> omega
  · rw [drop_past _ _ _ (by omega), occurs_drop_iff]
    split <;> omega

def invCount : List ℕ → ℕ
  | [] => 0
  | a::w => w.countP (· < a) + invCount w

theorem invCount_insert (L R : List ℕ) (positive : 0 ∉ L) :
    invCount (L++0::R) = invCount (L++R)+L.length := by
  induction L with
  | nil => simp [invCount]
  | cons a L ih =>
    have ha : 0<a := by have hn : a≠0 := fun e => positive (by simp [e]); omega
    have hp : 0 ∉ L := fun e => positive (by simp [e])
    simp only [List.cons_append, invCount, List.length_cons, List.countP_append,
      List.countP_cons, decide_eq_true_eq, ha, ite_true, ih hp]
    omega

end StableInversions
