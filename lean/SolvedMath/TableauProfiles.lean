import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity

namespace PeriodicTableaux

abbrev Bond (n : ℕ) := Fin (n+1)
abbrev Heights (n : ℕ) := Bond n → ℤ
abbrev Cell (n : ℕ) := Bond n × ℤ

/-- The plane coordinates of the cell (i,k) are (k,k+i). -/
def Below {n : ℕ} (a b : Cell n) : Prop :=
  a.2 ≤ b.2 ∧ a.2 + (a.1 : ℤ) ≤ b.2 + (b.1 : ℤ)

def Before {n : ℕ} (a b : Cell n) : Prop := Below a b ∧ a ≠ b

def Profile {n : ℕ} (h : Heights n) : Prop :=
  ∀ i j, i ≤ j → h j ≤ h i ∧ h i + (i : ℤ) ≤ h j + (j : ℤ)

def Inside {n : ℕ} (h : Heights n) (a : Cell n) : Prop := a.2 ≤ h a.1

def Seen {n : ℕ} (p h : Heights n) (a : Cell n) : Prop := ¬ Inside p a ∧ Inside h a

def top {n : ℕ} (h : Heights n) (i : Bond n) : Cell n := (i,h i)

@[simp] theorem top_fst {n} (h : Heights n) (i : Bond n) : (top h i).1 = i := rfl

def raise {n : ℕ} (h : Heights n) (i : Bond n) : Heights n := Function.update h i (h i+1)
def lower {n : ℕ} (h : Heights n) (i : Bond n) : Heights n := Function.update h i (h i-1)

@[simp] theorem raise_at {n} (h : Heights n) (i : Bond n) : raise h i i = h i + 1 := by simp [raise]
@[simp] theorem lower_at {n} (h : Heights n) (i : Bond n) : lower h i i = h i - 1 := by simp [lower]
@[simp] theorem raise_lower {n} (h : Heights n) (i : Bond n) : raise (lower h i) i = h := by
  funext j
  by_cases he : j = i <;> simp [raise, lower, Function.update, he]
@[simp] theorem lower_raise {n} (h : Heights n) (i : Bond n) : lower (raise h i) i = h := by
  funext j
  by_cases he : j = i <;> simp [raise, lower, Function.update, he]

theorem profile_iff_ideal {n} (h : Heights n) :
    Profile h ↔ ∀ a b, Below a b → Inside h b → Inside h a := by
  constructor
  · rintro hp ⟨i,k⟩ ⟨j,l⟩ ⟨h₁,h₂⟩ hb
    change l ≤ h j at hb
    change k ≤ l at h₁
    change k + (i : ℤ) ≤ l + (j : ℤ) at h₂
    change k ≤ h i
    rcases le_total i j with hij | hji
    · exact h₁.trans (hb.trans (hp i j hij).1)
    · have hh := (hp j i hji).2
      omega
  · intro H i j hij
    have hij' : (i : ℤ) ≤ (j : ℤ) := by exact_mod_cast hij
    constructor
    · apply H (i,h j) (j,h j) <;> simp [Below, Inside, hij']
    · have q := H (j,h i + i - j) (i,h i) (by
        constructor <;> dsimp <;> omega) (le_refl _)
      change h i + i - j ≤ h j at q
      omega

theorem inside_lower {n} (h : Heights n) (i : Bond n) (a : Cell n) :
    Inside (lower h i) a ↔ Inside h a ∧ a ≠ top h i := by
  rcases a with ⟨j,k⟩
  by_cases e : j = i
  · subst j
    simp [Inside, top]
    omega
  · simp [Inside, top, lower, Function.update, e]

theorem inside_raise {n} (h : Heights n) (i : Bond n) (a : Cell n) :
    Inside (raise h i) a ↔ Inside h a ∨ a = top (raise h i) i := by
  rcases a with ⟨j,k⟩
  by_cases e : j = i
  · subst j
    simp [Inside, top]
    omega
  · simp [Inside, top, raise, Function.update, e]

theorem maximal_iff_lower {n} {h : Heights n} (hh : Profile h) (i : Bond n) :
    (∀ b, Inside h b → ¬ Before (top h i) b) ↔ Profile (lower h i) := by
  rw [profile_iff_ideal]
  constructor
  · intro hm a b hab hb
    rw [inside_lower] at hb ⊢
    refine ⟨(profile_iff_ideal _).mp hh a b hab hb.1, ?_⟩
    rintro rfl
    exact hm b hb.1 ⟨hab, hb.2.symm⟩
  · intro hlow b hb hbad
    have hin : Inside (lower h i) b := (inside_lower ..).mpr ⟨hb,hbad.2.symm⟩
    have htop := hlow _ _ hbad.1 hin
    exact ((inside_lower ..).mp htop).2 rfl

/-- Newest cell first. Pairwise forbids a later occurrence of a strict predecessor. -/
def History {n : ℕ} (p h : Heights n) (l : List (Cell n)) : Prop :=
  (∀ a, a ∈ l ↔ Seen p h a) ∧ l.Pairwise (fun newer older => ¬ Before newer older)

theorem empty_history {n} (p : Heights n) : History p p [] := by simp [History, Seen]

theorem history_top {n} {p h : Heights n} (hp : Profile p) (hh : Profile h) {a : Cell n} {l : List (Cell n)}
    (hw : History p h (a :: l)) :
    a = top h a.1 ∧ p a.1 < h a.1 ∧ Profile (lower h a.1) := by
  have ha := (hw.1 a).mp (by simp)
  have hma (b : Cell n) (hb : Inside h b) : ¬ Before a b := by
    intro hbad
    have hn : ¬ Inside p b := fun H => ha.1 ((profile_iff_ideal _).mp hp a b hbad.1 H)
    have hm := (hw.1 b).mpr ⟨hn,hb⟩
    rcases List.mem_cons.mp hm with he|he
    · exact hbad.2 he.symm
    · exact (List.pairwise_cons.mp hw.2).1 b he hbad
  have he : a = top h a.1 := by
    by_contra hne
    exact hma (top h a.1) (le_refl _) ⟨⟨ha.2,add_le_add_left ha.2 _⟩,hne⟩
  obtain ⟨i,k⟩ := a
  change (i,k) = (i,h i) at he
  have hk : k = h i := congrArg Prod.snd he
  subst k
  refine ⟨rfl, by exact lt_of_not_ge ha.1, ?_⟩
  exact (maximal_iff_lower hh i).mp hma

private theorem top_raised_new {n} (h : Heights n) (i : Bond n) :
    ¬ Inside h (top (raise h i) i) := by simp [Inside, top]

theorem history_raise {n} {p h : Heights n} (hh : Profile h) (hle : p ≤ h)
    {l : List (Cell n)} (hw : History p h l) (i : Bond n) :
    History p (raise h i) (top (raise h i) i :: l) := by
  have hnew : ¬ Inside p (top (raise h i) i) := by
    simp only [Inside,top,raise_at]
    have hi : p i ≤ h i := hle i
    omega
  constructor
  · intro a
    rw [List.mem_cons, hw.1]
    simp only [Seen, inside_raise]
    by_cases e : a = top (raise h i) i <;> simp_all
  · rw [List.pairwise_cons]
    refine ⟨?_,hw.2⟩
    intro b hb hbad
    exact top_raised_new h i ((profile_iff_ideal _).mp hh _ b hbad.1 ((hw.1 _).mp hb).2)

theorem history_repeat {n} {p h : Heights n} (hh : Profile h) {l : List (Cell n)}
    (hw : History p h l) (i : Bond n) (hi : p i < h i) (hl : Profile (lower h i)) :
    History p h (top h i :: l) := by
  have hseen : Seen p h (top h i) := ⟨not_le.mpr hi,le_refl _⟩
  constructor
  · intro a
    rw [List.mem_cons, hw.1]
    exact or_iff_right_of_imp fun he => he ▸ hseen
  · rw [List.pairwise_cons]
    exact ⟨fun b hb => (maximal_iff_lower hh i).mpr hl b ((hw.1 b).mp hb).2, hw.2⟩

abbrev Mark (n : ℕ) := Bool × Bond n

inductive Trace {n : ℕ} (p : Heights n) :
    Heights n → List (Mark n) → List (Cell n) → Prop
  | nil : Trace p p [] []
  | discover {h ops l} (t : Trace p h ops l) (i : Bond n) (enabled : Profile (raise h i)) :
      Trace p (raise h i) ((true,i)::ops) (top (raise h i) i::l)
  | repeatCell {h ops l} (t : Trace p h ops l) (i : Bond n) (seen : p i < h i)
      (removable : Profile (lower h i)) : Trace p h ((false,i)::ops) (top h i::l)

theorem Trace.sound {n} {p h : Heights n} {ops l} (hp : Profile p) (t : Trace p h ops l) :
    Profile h ∧ p ≤ h ∧ History p h l := by
  induction t with
  | nil => exact ⟨hp,le_refl _,empty_history p⟩
  | discover t i en ih =>
    refine ⟨en,fun j => ?_,history_raise ih.1 ih.2.1 ih.2.2 i⟩
    by_cases he : j = i
    · subst j
      exact (ih.2.1 i).trans (by simp)
    · simpa [raise, Function.update, he] using ih.2.1 j
  | repeatCell t i seen removable ih =>
    exact ⟨ih.1,ih.2.1,history_repeat ih.1 ih.2.2 i seen removable⟩

def tags {n} : List (Cell n) → List (Mark n)
  | [] => []
  | a::l => (decide (a ∉ l),a.1) :: tags l

theorem trace_of_history {n} {p : Heights n} (hp : Profile p) (l : List (Cell n))
    (h : Heights n) (hh : Profile h) (hle : p ≤ h) (hw : History p h l) :
    Trace p h (tags l) l := by
  induction l generalizing h with
  | nil =>
    have he : p = h := by
      funext i
      apply le_antisymm (hle i)
      by_contra! hlt
      have ha := (hw.1 (top h i)).mpr ⟨not_le.mpr hlt,le_refl _⟩
      simp at ha
    subst h
    exact Trace.nil
  | cons a l ih =>
    obtain ⟨i,k⟩ := a
    obtain ⟨he,hpi,hl⟩ := history_top hp hh hw
    have hk : k = h i := congrArg Prod.snd he
    subst k
    change History p h (top h i :: l) at hw
    by_cases hmem : top h i ∈ l
    · have hw' : History p h l := by
        refine ⟨fun a => ?_,(List.pairwise_cons.mp hw.2).2⟩
        rw [← hw.1, List.mem_cons]
        exact (or_iff_right_of_imp fun eq => eq ▸ hmem).symm
      change Trace p h (tags (top h i :: l)) (top h i :: l)
      simpa [tags, hmem] using (Trace.repeatCell (ih h hh hle hw') i hpi hl)
    · have hle' : p ≤ lower h i := by
        intro j
        by_cases eq : j = i
        · subst j
          change p i ≤ lower h i i
          rw [lower_at]
          change p i < h i at hpi
          omega
        · simpa [lower, Function.update, eq] using hle j
      have hw' : History p (lower h i) l := by
        refine ⟨fun a => ?_,(List.pairwise_cons.mp hw.2).2⟩
        have hm := hw.1 a
        simp only [List.mem_cons, Seen] at hm
        simp only [Seen, inside_lower]
        by_cases eq : a = top h i <;> aesop
      have t := Trace.discover (ih (lower h i) hl hle' hw') i (by simpa using hh)
      change Trace p h (tags (top h i :: l)) (top h i :: l)
      simpa [tags, hmem] using t

theorem Trace.tags_eq {n} {p h : Heights n} {ops l} (hp : Profile p) (t : Trace p h ops l) :
    tags l = ops := by
  induction t with
  | nil => rfl
  | discover t i en ih =>
    have hnew : top (raise _ i) i ∉ _ := fun hm =>
      top_raised_new _ i (((t.sound hp).2.2.1 _).mp hm).2
    simp [tags,hnew,ih]
  | repeatCell t i hi hl ih =>
    have hm := ((t.sound hp).2.2.1 _).mpr (show Seen _ _ (top _ i) from ⟨not_le.mpr hi,le_refl _⟩)
    simp [tags,hm,ih]


def finalH {n} (p : Heights n) : List (Mark n) → Heights n
  | [] => p
  | (true,i)::ops => raise (finalH p ops) i
  | (false,_)::ops => finalH p ops

def readCells {n} (p : Heights n) : List (Mark n) → List (Cell n)
  | [] => []
  | op::ops => top (finalH p (op::ops)) op.2 :: readCells p ops

theorem Trace.final_eq {n} {p h : Heights n} {ops l} (t : Trace p h ops l) :
    finalH p ops = h := by
  induction t with
  | nil => rfl
  | discover t i en ih => simp only [finalH, ih]
  | repeatCell t i hi hl ih => exact ih

theorem Trace.cells_eq {n} {p h : Heights n} {ops l} (t : Trace p h ops l) :
    readCells p ops = l := by
  induction t with
  | nil => rfl
  | discover t i en ih => simp only [readCells,finalH,t.final_eq,ih]
  | repeatCell t i hi hl ih => simp only [readCells,finalH,t.final_eq,ih]

@[simp] theorem length_readCells {n} (p : Heights n) (ops : List (Mark n)) :
    (readCells p ops).length = ops.length := by induction ops <;> simp_all [readCells]

@[simp] theorem length_tags {n} (l : List (Cell n)) :
    (tags l).length = l.length := by induction l <;> simp_all [tags]

def volume {n} (p h : Heights n) : ℤ := ∑ i, (h i-p i)

def freshCount {n} (ops : List (Mark n)) : ℕ := ops.countP Prod.fst

theorem volume_raise {n} (p h : Heights n) (i : Bond n) :
    volume p (raise h i) = volume p h + 1 := by
  have eq (j : Bond n) : raise h i j - p j = (h j - p j) + (if i=j then 1 else 0) := by
    by_cases he : j = i
    · subst j
      simp
      omega
    · simp [raise,Function.update,he,Ne.symm he]
  simp [volume, eq, Finset.sum_add_distrib]

theorem volume_final {n} (p : Heights n) (ops : List (Mark n)) :
    volume p (finalH p ops) = (freshCount ops : ℤ) := by
  induction ops with
  | nil => simp [volume,finalH,freshCount]
  | cons op ops ih =>
    obtain ⟨b,i⟩ := op
    cases b <;> simp_all [finalH, freshCount, volume_raise]

end PeriodicTableaux
