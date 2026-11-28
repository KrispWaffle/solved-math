module

public import SolvedMath.StableInversions
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace StableInversions

theorem shape_succ_map (r : ℕ) (w : List ℕ) : shape r (w.map Nat.succ) ↔ shape r w := by
  induction r generalizing w with
  | zero =>
    rcases w with _ | ⟨a, _ | ⟨b, _ | ⟨c, w⟩⟩⟩ <;> simp [shape]
  | succ r ih =>
    cases w with
    | nil => simp [shape]
    | cons a w => simp [shape, ih]

theorem occurs_succ_map (r : ℕ) (w : List ℕ) : occurs r (w.map Nat.succ) ↔ occurs r w := by
  constructor
  · rintro ⟨v, hv, hs⟩
    obtain ⟨u, hu, rfl⟩ := List.sublist_map_iff.1 hs
    exact ⟨u, (shape_succ_map _ _).1 hv, hu⟩
  · rintro ⟨u, hu, hs⟩
    exact ⟨u.map Nat.succ, (shape_succ_map _ _).2 hu, hs.map _⟩

@[simp] theorem cutoff_succ_map (r : ℕ) (w : List ℕ) : cutoff r (w.map Nat.succ) = cutoff r w := by
  classical
  induction w with
  | nil => rfl
  | cons a w ih =>
    change (if occurs r ((a::w).map Nat.succ) then cutoff r (w.map Nat.succ) + 1 else 0) = _
    rw [occurs_succ_map, ih]
    rfl

@[simp] theorem invCount_succ_map (w : List ℕ) : invCount (w.map Nat.succ) = invCount w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp [invCount, ih, List.countP_map, Function.comp_def]

/-- Store the most recent insertion first, so removing the minimum removes the head slot. -/
def insertMinimum (i : ℕ) (w : List ℕ) : List ℕ :=
  (w.take i).map Nat.succ ++ 0 :: (w.drop i).map Nat.succ

def realize : List ℕ → List ℕ
  | [] => []
  | i::h => insertMinimum i (realize h)

def nextState (s : ℕ × ℕ) (i : ℕ) : ℕ × ℕ := if i < s.2 then (i+1,s.2+1) else (s.1,i)

def state : List ℕ → ℕ × ℕ
  | [] => (0,0)
  | i::h => nextState (state h) i

def admissible : List ℕ → Prop
  | [] => True
  | i::h => admissible h ∧ (state h).1 ≤ i ∧ i ≤ h.length

@[simp] theorem realize_length (h : List ℕ) : (realize h).length = h.length := by
  induction h with
  | nil => rfl
  | cons i h ih => simp [realize, insertMinimum, ih]; omega

private theorem split_lift (w : List ℕ) (i : ℕ) :
    (w.take i).map Nat.succ ++ (w.drop i).map Nat.succ = w.map Nat.succ := by
  rw [← List.map_append, List.take_append_drop]

private theorem lift_pos (w : List ℕ) : 0 ∉ w.map Nat.succ := by simp

theorem realize_perm (h : List ℕ) : (realize h).Perm (List.range h.length) := by
  induction h with
  | nil => rfl
  | cons i h ih =>
    rw [realize, insertMinimum, List.length_cons, List.range_succ_eq_map]
    apply List.Perm.trans List.perm_middle
    rw [split_lift]
    exact (ih.map _).cons _

theorem insertMinimum_avoid (w : List ℕ) (i : ℕ) (hi : i≤w.length) (old : ¬ occurs 2 w) :
    ¬ occurs 2 (insertMinimum i w) ↔ cutoff 1 w ≤ i := by
  unfold insertMinimum
  have hp := avoids1243_insert ((w.take i).map Nat.succ) ((w.drop i).map Nat.succ)
    (lift_pos _) (lift_pos _) (by rw [split_lift, occurs_succ_map]; exact old)
  simpa [split_lift, Nat.min_eq_left hi] using hp

theorem insertMinimum_state (w : List ℕ) (i : ℕ) (hi : i≤w.length) (legal : cutoff 1 w ≤ i) :
    (cutoff 1 (insertMinimum i w), cutoff 0 (insertMinimum i w)) =
      nextState (cutoff 1 w, cutoff 0 w) i := by
  unfold insertMinimum nextState
  have h0 := cutoff_inversion_insert ((w.take i).map Nat.succ) ((w.drop i).map Nat.succ) (lift_pos _)
  have h1 := cutoff_132_insert ((w.take i).map Nat.succ) ((w.drop i).map Nat.succ)
    (lift_pos _) (lift_pos _) (by simpa [split_lift, Nat.min_eq_left hi] using legal)
  simp only [List.length_map, List.length_take, Nat.min_eq_left hi, split_lift, cutoff_succ_map] at h0 h1
  rw [h0,h1]; split <;> rfl

theorem insertMinimum_weight (w : List ℕ) (i : ℕ) (hi : i≤w.length) :
    invCount (insertMinimum i w) = invCount w + i := by
  unfold insertMinimum
  simpa [split_lift, Nat.min_eq_left hi] using
    invCount_insert ((w.take i).map Nat.succ) ((w.drop i).map Nat.succ) (lift_pos _)

theorem realize_behavior (h : List ℕ) (legal : admissible h) :
    ¬ occurs 2 (realize h) ∧ (cutoff 1 (realize h),cutoff 0 (realize h)) = state h ∧
    invCount (realize h) = h.sum := by
  induction h with
  | nil => exact ⟨not_occurs_nil _, rfl, rfl⟩
  | cons i h ih =>
    obtain ⟨hlegal, ha, hi⟩ := legal
    obtain ⟨avoids, pair, hinv⟩ := ih hlegal
    have le : cutoff 1 (realize h) ≤ i := by simpa [← pair] using ha
    have li : i ≤ (realize h).length := by simpa using hi
    exact ⟨(insertMinimum_avoid _ _ li avoids).2 le, (insertMinimum_state _ _ li le).trans (by rw [pair]; rfl),
      (insertMinimum_weight _ _ li).trans (by simp [hinv, Nat.add_comm])⟩

private theorem locate_insert (i : ℕ) (w : List ℕ) (hi : i≤w.length) : (insertMinimum i w).idxOf 0 = i := by
  unfold insertMinimum
  rw [List.idxOf_append_of_notMem (lift_pos _)]
  simp [hi]

private theorem undo_insert (i : ℕ) (w : List ℕ) : ((insertMinimum i w).erase 0).map Nat.pred = w := by
  unfold insertMinimum
  rw [List.erase_append_right _ (lift_pos _), List.erase_cons_head, split_lift]
  simp [List.map_map, Function.comp_def]

theorem realize_unique {h h' : List ℕ} (hh : admissible h) (hh' : admissible h')
    (eq : realize h = realize h') : h=h' := by
  induction h generalizing h' with
  | nil =>
    have len := congrArg List.length eq
    simp only [realize_length, List.length_nil] at len
    exact (List.length_eq_zero_iff.1 len.symm).symm
  | cons i h ih =>
    cases h' with
    | nil => have len := congrArg List.length eq; simp at len
    | cons j h' =>
      obtain ⟨hp,_,hi⟩ := hh
      obtain ⟨hp',_,hj⟩ := hh'
      change insertMinimum i (realize h) = insertMinimum j (realize h') at eq
      have slots := congrArg (fun w : List ℕ => w.idxOf 0) eq
      change (insertMinimum i (realize h)).idxOf 0 = (insertMinimum j (realize h')).idxOf 0 at slots
      rw [locate_insert i (realize h) (by simpa using hi), locate_insert j (realize h') (by simpa using hj)] at slots
      have old := congrArg (fun w : List ℕ => (w.erase 0).map Nat.pred) eq
      change ((insertMinimum i (realize h)).erase 0).map Nat.pred = ((insertMinimum j (realize h')).erase 0).map Nat.pred at old
      rw [undo_insert, undo_insert] at old
      exact List.cons.injEq _ _ _ _ |>.mpr ⟨slots, ih hp hp' old⟩

private theorem lower_raise (w : List ℕ) (pos : 0 ∉ w) : (w.map Nat.pred).map Nat.succ = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have ha : 0<a := by have hn : a≠0 := fun e => pos (by simp [e]); omega
    have hp : 0 ∉ w := fun e => pos (by simp [e])
    simp [ih hp]; omega

/-- Every classical 1243-avoiding permutation yields an admissible insertion history. -/
theorem realize_surjective (n : ℕ) (w : List ℕ) (perm : w.Perm (List.range n))
    (avoids : ¬ occurs 2 w) : ∃ h, admissible h ∧ h.length=n ∧ realize h=w := by
  induction n generalizing w with
  | zero => exact ⟨[], trivial, rfl, perm.eq_nil.symm⟩
  | succ n ih =>
    rw [List.range_succ_eq_map] at perm
    obtain ⟨L,R,rfl,_⟩ := List.eq_append_cons_of_mem (perm.mem_iff.mpr (by simp : 0 ∈ 0::(List.range n).map Nat.succ))
    have oldPerm := (List.perm_middle.symm.trans perm).cons_inv
    have hp : 0 ∉ L++R := fun e => lift_pos _ (oldPerm.mem_iff.mp e)
    let w := (L++R).map Nat.pred
    have lifted : w.map Nat.succ = L++R := lower_raise _ hp
    have wp : w.Perm (List.range n) := by simpa [w, List.map_map, Function.comp_def] using oldPerm.map Nat.pred
    have hi : L.length ≤ w.length := by simp [w]
    have back : insertMinimum L.length w = L++0::R := by simp [insertMinimum, lifted]
    have hw : ¬ occurs 2 w := by
      intro bad
      have hb : occurs 2 (L++R) := lifted ▸ (occurs_succ_map 2 w).2 bad
      exact avoids ((occurs_succ_insert 1 L R (fun e => hp (List.mem_append_left R e)) (fun e => hp (List.mem_append_right L e))).2 (Or.inl hb))
    obtain ⟨h,hl,hn,he⟩ := ih w wp hw
    have ok : cutoff 1 w ≤ L.length := (insertMinimum_avoid w _ hi hw).1 (back ▸ avoids)
    have pair := (realize_behavior h hl).2.1
    rw [he] at pair
    exact ⟨L.length::h, ⟨hl, by simpa [← pair] using ok, by simpa [← he] using hi⟩,
      by simp [hn], by simpa [realize, he] using back⟩

/-- Length and inversion count of the source avoider, with an actual permutation of [0,n). -/
abbrev Avoider (n k : ℕ) := {w : List ℕ // w.Perm (List.range n) ∧ ¬ occurs 2 w ∧ invCount w=k}

abbrev Histories (n k : ℕ) := {h : List ℕ // admissible h ∧ h.length=n ∧ h.sum=k}

noncomputable def historyEquiv (n k : ℕ) : Histories n k ≃ Avoider n k := by
  let f : Histories n k → Avoider n k := fun ⟨h,hl,hn,hk⟩ =>
    ⟨realize h, hn ▸ realize_perm h, (realize_behavior _ hl).1, (realize_behavior _ hl).2.2.trans hk⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y eq
    apply Subtype.ext
    exact realize_unique x.2.1 y.2.1 (congrArg Subtype.val eq)
  · rintro ⟨w,wp,wa,wk⟩
    obtain ⟨h,hl,hn,he⟩ := realize_surjective n w wp wa
    have hk : h.sum=k := (realize_behavior _ hl).2.2.symm.trans (he ▸ wk)
    exact ⟨⟨h,hl,hn,hk⟩, Subtype.ext he⟩

instance (n k : ℕ) : Finite (Avoider n k) := by
  classical
  let f : Avoider n k → ↥((List.range n).permutations.toFinset) :=
    fun w => ⟨w.1, by simpa using w.2.1⟩
  apply Finite.of_injective f
  intro x y h
  exact Subtype.ext (congrArg (fun t : ↥((List.range n).permutations.toFinset) => t.val) h)

instance (n k : ℕ) : Finite (Histories n k) := Finite.of_equiv _ (historyEquiv n k).symm

noncomputable def sourceCount (n k : ℕ) : ℕ := Nat.card (Avoider n k)

theorem sourceCount_eq_histories (n k : ℕ) : sourceCount n k = Nat.card (Histories n k) :=
  Nat.card_congr (historyEquiv n k).symm

end StableInversions
