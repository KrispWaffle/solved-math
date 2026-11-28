module

public import Mathlib.Data.List.Forall2
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Tauto

@[expose] public section

namespace LayeredRanks

/-- Positive letters embedded in order, bounded by their chosen capacities. -/
abbrev Embeds (u w : List ℕ) : Prop :=
  List.SublistForall₂ (fun a b : ℕ => 0 < a ∧ a ≤ b) u w

def greedy : List ℕ → List ℕ → Option (List Bool)
  | [], [] => some []
  | [], _::_ => none
  | _::w, [] => some (List.replicate (w.length+1) false)
  | b::w, a::u => if 0 < a ∧ a ≤ b then (greedy w u).map (true :: ·)
      else (greedy w (a::u)).map (false :: ·)

private theorem tail_embeds {a : ℕ} {u w : List ℕ} (h : Embeds (a::u) w) :
    Embeds u w := by
  induction w with
  | nil => cases h
  | cons b w ih =>
    cases h with
    | cons _ ht => exact .cons_right ht
    | cons_right ht => exact .cons_right (ih ht)

theorem greedy_succeeds_iff (w u : List ℕ) :
    (∃ mask, greedy w u = some mask) ↔ Embeds u w := by
  induction w generalizing u with
  | nil =>
    cases u with
    | nil => exact ⟨fun _ => .nil, fun _ => ⟨[], rfl⟩⟩
    | cons a u => constructor <;> intro h
                  · simp [greedy] at h
                  · cases h
  | cons b w ih =>
    cases u with
    | nil => exact ⟨fun _ => .nil, fun _ => ⟨_, rfl⟩⟩
    | cons a u =>
      by_cases h : 0 < a ∧ a ≤ b
      · constructor
        · intro he
          obtain ⟨mask, hm⟩ := he
          cases e : greedy w u with
          | none => simp [greedy, h, e] at hm
          | some m => exact .cons h ((ih u).1 ⟨m, e⟩)
        · intro he
          have hu : Embeds u w := by
            cases he with
            | cons _ ht => exact ht
            | cons_right ht => exact tail_embeds ht
          obtain ⟨m, hm⟩ := (ih u).2 hu
          exact ⟨true::m, by simp [greedy, h, hm]⟩
      · constructor
        · rintro ⟨mask, hm⟩
          cases e : greedy w (a::u) with
          | none => simp [greedy, h, e] at hm
          | some m => exact .cons_right ((ih _).1 ⟨m, e⟩)
        · intro he
          have hu : Embeds (a::u) w := by
            cases he with
            | cons ha _ => exact (h ha).elim
            | cons_right ht => exact ht
          obtain ⟨m, hm⟩ := (ih _).2 hu
          exact ⟨false::m, by simp [greedy, h, hm]⟩

/-- The pending maximum records the capacities skipped since the last selection. -/
def InBox : ℕ → List ℕ → List Bool → List ℕ → Prop
  | _, [], [], [] => True
  | bound, b::w, false::mask, u => InBox (max bound b) w mask u
  | bound, b::w, true::mask, a::u => bound < a ∧ a ≤ b ∧ InBox 0 w mask u
  | _, _, _, _ => False

private theorem empty_box (bound : ℕ) (w : List ℕ) (mask : List Bool) :
    InBox bound w mask [] ↔ mask = List.replicate w.length false := by
  induction w generalizing bound mask with
  | nil => cases mask <;> simp [InBox]
  | cons b w ih =>
    cases mask with
    | nil => simp [InBox]
    | cons bit mask =>
      cases bit <;> simp [InBox, List.replicate_succ, ih]

private theorem first_positive {w : List ℕ} {d : ℕ} {v : List ℕ}
    (h : Embeds (d::v) w) : 0 < d := by
  induction w with
  | nil => cases h
  | cons b w ih =>
    cases h with
    | cons hd _ => exact hd.1
    | cons_right ht => exact ih ht

/-- Each actual word has precisely the support picked by the greedy algorithm.
The additional lower bound only constrains the first letter. -/
theorem inBox_iff (bound : ℕ) (w : List ℕ) (mask : List Bool) (u : List ℕ) :
    InBox bound w mask u ↔ greedy w u = some mask ∧ (∀ a v, u = a::v → bound < a) := by
  induction w generalizing bound mask u with
  | nil =>
    cases u <;> cases mask <;> simp [InBox, greedy]
  | cons b w ih =>
    cases u with
    | nil => simp [empty_box, greedy, eq_comm]
    | cons a u =>
      by_cases ha : 0 < a ∧ a ≤ b
      · cases mask with
        | nil => simp [InBox, greedy, ha]
        | cons bit mask =>
          cases bit with
          | false => simp [InBox, ih, greedy, ha, max_lt_iff]
          | true =>
            simp [InBox, ih, greedy, ha]
            have hpos : greedy w u = some mask → ∀ d v, u = d::v → 0 < d := by
              rintro found d v rfl
              exact first_positive ((greedy_succeeds_iff _ _).1 ⟨mask, found⟩)
            tauto
      · cases mask with
        | nil => simp [InBox, greedy, ha]
        | cons bit mask =>
          cases bit with
          | false => simp [InBox, ih, greedy, ha, max_lt_iff]; omega
          | true => simp [InBox, greedy, ha]; omega

/-- Embeddable positive compositions admit exactly one of the indicated boxes. -/
theorem embeds_iff_unique_box (u w : List ℕ) : Embeds u w ↔ ∃! mask, InBox 0 w mask u := by
  constructor
  · intro h
    obtain ⟨mask, hm⟩ := (greedy_succeeds_iff w u).2 h
    refine ⟨mask, (inBox_iff _ _ _ _).2 ⟨hm, ?_⟩, ?_⟩
    · rintro a v rfl
      exact first_positive h
    · intro other ho
      have hh := ((inBox_iff _ _ _ _).1 ho).1
      exact Option.some.inj (hh.symm.trans hm)
  · rintro ⟨mask, hm, _⟩
    exact (greedy_succeeds_iff w u).1 ⟨mask, ((inBox_iff _ _ _ _).1 hm).1⟩

/-- Enumerate actual generalized subwords, coalescing repeated embeddings. -/
def subwords : List ℕ → Finset (List ℕ)
  | [] => {[]}
  | b::w => subwords w ∪ (Finset.Icc 1 b).biUnion (fun a => (subwords w).image (a :: ·))

theorem mem_subwords {u w : List ℕ} : u ∈ subwords w ↔ Embeds u w := by
  induction w generalizing u with
  | nil =>
    cases u with
    | nil => exact ⟨fun _ => .nil, fun _ => by simp [subwords]⟩
    | cons a v => constructor <;> intro h
                  · simp [subwords] at h
                  · cases h
  | cons b w ih =>
    simp only [subwords, Finset.mem_union, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro (h | ⟨a, ha, v, hv, rfl⟩)
      · exact .cons_right (ih.1 h)
      · exact .cons ha (ih.1 hv)
    · intro h
      cases h with
      | nil => exact Or.inl (ih.2 .nil)
      | cons ha hv => exact Or.inr ⟨_, ha, _, ih.2 hv, rfl⟩
      | cons_right hv => exact Or.inl (ih.2 hv)

def masks : List ℕ → Finset (List Bool)
  | [] => {[]}
  | _::w => (masks w).image (false :: ·) ∪ (masks w).image (true :: ·)

theorem masks_length {w : List ℕ} {m : List Bool} : m ∈ masks w ↔ m.length = w.length := by
  induction w generalizing m with
  | nil => simp [masks]
  | cons b w ih =>
    cases m with
    | nil => simp [masks]
    | cons bit m => cases bit <;> simp [masks, ih]

def boxWords : ℕ → List ℕ → List Bool → Finset (List ℕ)
  | _, [], [] => {[]}
  | bound, b::w, false::m => boxWords (max bound b) w m
  | bound, b::w, true::m => (Finset.Icc (bound+1) b).biUnion
      (fun a => (boxWords 0 w m).image (a :: ·))
  | _, _, _ => ∅

theorem mem_boxWords (bound : ℕ) (w : List ℕ) (mask : List Bool) (u : List ℕ) :
    u ∈ boxWords bound w mask ↔ InBox bound w mask u := by
  induction w generalizing bound mask u with
  | nil => cases mask <;> cases u <;> simp [boxWords, InBox]
  | cons b w ih =>
    cases mask with
    | nil => cases u <;> simp [boxWords, InBox]
    | cons bit mask =>
      cases bit with
      | false => exact ih _ _ _
      | true =>
        cases u <;> simp [boxWords, InBox, ih, and_assoc, Nat.succ_le_iff]

theorem box_mask_length {bound : ℕ} {w : List ℕ} {mask : List Bool} {u : List ℕ}
    (h : InBox bound w mask u) : mask.length = w.length := by
  induction w generalizing bound mask u with
  | nil => cases mask <;> cases u <;> simp_all [InBox]
  | cons b w ih =>
    cases mask with
    | nil => cases u <;> simp [InBox] at h
    | cons bit mask =>
      cases bit with
      | false => exact congrArg Nat.succ (ih h)
      | true =>
        cases u with
        | nil => simp [InBox] at h
        | cons a u => exact congrArg Nat.succ (ih h.2.2)

/-- The literal cardinality of the finite set of distinct compositions of weight r. -/
def rankCount (w : List ℕ) (r : ℕ) := ((subwords w).filter (fun u => u.sum = r)).card

def boxCount (w : List ℕ) (mask : List Bool) (r : ℕ) :=
  ((boxWords 0 w mask).filter (fun u => u.sum = r)).card

theorem rankCount_eq_sum_boxes (w : List ℕ) (r : ℕ) :
    rankCount w r = ∑ mask ∈ masks w, boxCount w mask r := by
  classical
  let F (m : List Bool) := (boxWords 0 w m).filter (fun u => u.sum = r)
  have eq : (subwords w).filter (fun u => u.sum = r) = (masks w).biUnion F := by
    ext u
    simp only [Finset.mem_filter, mem_subwords, Finset.mem_biUnion]
    constructor
    · rintro ⟨emb, hr⟩
      obtain ⟨m, hm, _⟩ := (embeds_iff_unique_box u w).1 emb
      exact ⟨m, masks_length.2 (box_mask_length hm), Finset.mem_filter.2
        ⟨(mem_boxWords _ _ _ _).2 hm, hr⟩⟩
    · rintro ⟨m, _, hu⟩
      obtain ⟨hm, hr⟩ := Finset.mem_filter.1 hu
      have hg := ((inBox_iff _ _ _ _).1 ((mem_boxWords _ _ _ _).1 hm)).1
      exact ⟨(greedy_succeeds_iff w u).1 ⟨m, hg⟩, hr⟩
  unfold rankCount
  rw [eq]
  apply Finset.card_biUnion
  intro m _ m' _ hne
  apply Finset.disjoint_left.2
  intro u hu hu'
  have get (n : List Bool) (h : u ∈ F n) : greedy w u = some n :=
    ((inBox_iff _ _ _ _).1 ((mem_boxWords _ _ _ _).1 (Finset.mem_filter.1 h).1)).1
  exact hne (Option.some.inj ((get m hu).symm.trans (get m' hu')))

/-- Twice the center of a valid greedy box, computed directly from its gaps. -/
def twiceCenter : ℕ → List ℕ → List Bool → ℕ
  | bound, b::w, true::m => bound+1+b+twiceCenter 0 w m
  | bound, b::w, false::m => twiceCenter (max bound b) w m
  | _, _, _ => 0

theorem twiceCenter_le (bound : ℕ) (w : List ℕ) (mask : List Bool) :
    twiceCenter bound w mask ≤ bound + w.sum + mask.count true := by
  induction w generalizing bound mask with
  | nil => simp [twiceCenter]
  | cons b w ih =>
    cases mask with
    | nil => simp [twiceCenter]
    | cons bit m =>
      cases bit with
      | true =>
        have h := ih 0 m
        simp [twiceCenter] at *
        omega
      | false =>
        have h := ih (max bound b) m
        simp [twiceCenter] at *
        omega

end LayeredRanks
