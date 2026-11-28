import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity

namespace DistinctPermutationPatterns

open Finset Filter
open scoped Topology
noncomputable section

/-- Read a subset in position order; replace each value by its zero-based rank in the subset. -/
def pattern {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : List ℕ :=
  S.sort.map (fun a => (S.filter (fun b => π b < π a)).card)

theorem pattern_length {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    (pattern π S).length = S.card := by simp [pattern]

def distinctCount {n : ℕ} (π : Equiv.Perm (Fin n)) : ℕ :=
  ((univ : Finset (Fin n)).powerset.image (pattern π)).card

def fixedSizeCount {n : ℕ} (π : Equiv.Perm (Fin n)) (m : ℕ) : ℕ :=
  (((univ : Finset (Fin n)).powersetCard m).image (pattern π)).card

def occurrenceCount {n : ℕ} (π : Equiv.Perm (Fin n)) (P : List ℕ) : ℕ :=
  ((univ : Finset (Fin n)).powerset.filter (fun T => pattern π T = P)).card

/-- The normalized exact expectation in Borrás-Serrano–Byrne–Godbole–Veimau, §4. -/
def normalizedMean (n : ℕ) : ℝ :=
  (∑ π : Equiv.Perm (Fin n), (distinctCount π : ℝ)) / ((n.factorial:ℝ)*2^n)

def fixedSizeMean (n m : ℕ) : ℝ :=
  (∑ π : Equiv.Perm (Fin n), (fixedSizeCount π m : ℝ)) /
    ((n.factorial:ℝ)*(n.choose m:ℝ))

def ExactMeanLimit : Prop := Tendsto normalizedMean atTop (𝓝 (Real.exp (-2)))

private theorem image_card_by_fibers {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) :
    ((s.image f).card : ℝ) = ∑ x ∈ s, (((s.filter (fun y => f y=f x)).card : ℝ))⁻¹ := by
  classical
  let c := fun b : β => ((s.filter (fun x => f x=b)).card : ℝ)
  calc
    _ = ∑ b ∈ s.image f, (1:ℝ) := by simp
    _ = ∑ b ∈ s.image f, ∑ _x ∈ s.filter (fun x => f x=b), (c b)⁻¹ := by
      apply sum_congr rfl
      intro b hb
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hb
      have hpos : 0 < (s.filter (fun y => f y=f x)).card := by
        exact card_pos.mpr ⟨x,mem_filter.mpr ⟨hx,rfl⟩⟩
      have hz : c (f x) ≠ 0 := by
        dsimp [c]
        exact_mod_cast hpos.ne'
      simp [c,sum_const,nsmul_eq_mul,show ((s.filter (fun y => f y=f x)).card : ℝ) ≠ 0 from hz]
    _ = _ := sum_fiberwise_of_maps_to' (fun x hx => mem_image_of_mem f hx) (fun b => (c b)⁻¹)

theorem distinctCount_by_occurrences {n : ℕ} (π : Equiv.Perm (Fin n)) :
    (distinctCount π : ℝ) =
    ∑ S ∈ (univ : Finset (Fin n)).powerset, (occurrenceCount π (pattern π S) : ℝ)⁻¹ :=
  image_card_by_fibers _ _

theorem fixedSizeCount_by_occurrences {n : ℕ} (π : Equiv.Perm (Fin n)) (m : ℕ) :
    (fixedSizeCount π m : ℝ) =
    ∑ S ∈ (univ : Finset (Fin n)).powersetCard m, (occurrenceCount π (pattern π S) : ℝ)⁻¹ := by
  rw [fixedSizeCount,image_card_by_fibers]
  apply sum_congr rfl
  intro S hS
  have eq : ((univ : Finset (Fin n)).powersetCard m).filter (fun T => pattern π T=pattern π S) =
      (univ : Finset (Fin n)).powerset.filter (fun T => pattern π T=pattern π S) := by
    ext T
    simp only [mem_filter,mem_powersetCard,mem_powerset,subset_univ,true_and,and_iff_right_iff_imp]
    intro h
    have e := congrArg List.length h
    simpa only [pattern_length,(mem_powersetCard.mp hS).2] using e
  rw [eq,occurrenceCount]

theorem normalizedMean_by_occurrences (n : ℕ) :
    normalizedMean n =
    (∑ π : Equiv.Perm (Fin n), ∑ S ∈ (univ : Finset (Fin n)).powerset,
      (occurrenceCount π (pattern π S) : ℝ)⁻¹) / ((n.factorial:ℝ)*2^n) := by
  simp only [normalizedMean,distinctCount_by_occurrences]

/-- A label strictly between two candidate partners prevents a pointwise replacement. -/
def Between {α : Type*} [LT α] (a x b : α) := (a < x ∧ x < b) ∨ (b < x ∧ x < a)

private theorem outside_iff {α : Type*} [LinearOrder α] {a b x : α} (ha : x≠a) (hb : x≠b) :
    ¬ Between a x b ↔ ((x<a ↔ x<b) ∧ (a<x ↔ b<x)) := by
  unfold Between
  rcases lt_or_gt_of_ne ha with hxa|hax <;> rcases lt_or_gt_of_ne hb with hxb|hbx <;>
    simp_all [not_lt_of_gt]

def replaceRed {α : Type*} [DecidableEq α] (a b x : α) := if x=a then b else x

def preservesBoth {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (f : Fin n → Fin n) :=
  ∀ x ∈ S, ∀ y ∈ S, (x<y ↔ f x<f y) ∧ (π x<π y ↔ π (f x)<π (f y))

/-- The specific map moving a red label to a white label and fixing the other reds preserves
both orders exactly when neither open interval contains another red. -/
theorem single_replacement_iff {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    {a b : Fin n} (ha : a∈S) (hb : b∉S) :
    preservesBoth π S (replaceRed a b) ↔
    ∀ x ∈ S, x≠a → (¬Between a x b) ∧ (¬Between (π a) (π x) (π b)) := by
  constructor
  · intro h x hx hxa
    have hxb : x≠b := fun e => hb (e ▸ hx)
    have l := h x hx a ha
    have r := h a ha x hx
    simp only [replaceRed,ite_eq_right hxa,ite_true] at l r
    exact ⟨(outside_iff hxa hxb).mpr ⟨l.1,r.1⟩,
      (outside_iff (π.injective.ne hxa) (π.injective.ne hxb)).mpr ⟨l.2,r.2⟩⟩
  · intro h x hx y hy
    by_cases xa : x=a
    · subst x
      by_cases ya : y=a
      · subst y
        simp
      · have yb : y≠b := fun e => hb (e ▸ hy)
        obtain ⟨l,r⟩ := h y hy ya
        simpa [replaceRed,ya] using And.intro ((outside_iff ya yb).mp l).2
          ((outside_iff (π.injective.ne ya) (π.injective.ne yb)).mp r).2
    · by_cases ya : y=a
      · subst y
        have xb : x≠b := fun e => hb (e ▸ hx)
        obtain ⟨l,r⟩ := h x hx xa
        simpa [replaceRed,xa] using And.intro ((outside_iff xa xb).mp l).1
          ((outside_iff (π.injective.ne xa) (π.injective.ne xb)).mp r).1
      · simp [replaceRed,xa,ya]

/-- If an embedding of the labels preserves both restricted orders, its image has exactly the
same standardized rank list. -/
theorem pattern_map_of_preserves {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (e : Fin n ↪ Fin n) (h : preservesBoth π S e) : pattern π S = pattern π (S.map e) := by
  have mono : StrictMonoOn e (S : Set (Fin n)) := fun x hx y hy hxy => ((h x hx y hy).1).mp hxy
  unfold pattern
  rw [←StrictMonoOn.map_finsetSort e S mono,List.map_map]
  apply List.map_congr_left
  intro a ha
  have has : a∈S := mem_sort _ |>.mp ha
  simp only [Function.comp_apply,filter_map,card_map]
  apply congrArg card
  exact filter_congr (fun b hb => (h b hb a has).2)

/-- A pointwise allowable replacement produces a second occurrence of the source pattern. -/
theorem local_swap_pattern {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    {a b : Fin n} (ha : a∈S) (hb : b∉S)
    (gaps : ∀ x ∈ S, x≠a → (¬Between a x b) ∧ (¬Between (π a) (π x) (π b))) :
    pattern π S = pattern π (S.map (Equiv.swap a b).toEmbedding) := by
  apply pattern_map_of_preserves
  have hr := (single_replacement_iff π S ha hb).mpr gaps
  have same (x : Fin n) (hx : x∈S) : Equiv.swap a b x = replaceRed a b x := by
    by_cases hxa : x=a
    · simp [hxa,replaceRed]
    · have hxb : x≠b := fun eq => hb (eq ▸ hx)
      simp [replaceRed,hxa,Equiv.swap_apply_of_ne_of_ne hxa hxb]
  intro x hx y hy
  simpa only [Equiv.coe_toEmbedding,same x hx,same y hy] using hr x hx y hy

/-- Exact positive occurrence count for the pattern of every chosen subset. -/
theorem occurrenceCount_pos {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    0 < occurrenceCount π (pattern π S) := by
  exact card_pos.mpr ⟨S,mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),rfl⟩⟩

/-- An independent family of h choices giving distinct images of the same pattern gives
at least 2^h different occurrences. -/
theorem occurrenceCount_of_choices {n h : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    (choice : Finset (Fin h) → Finset (Fin n)) (inj : Function.Injective choice)
    (hp : ∀ U, pattern π (choice U)=pattern π S) : 2^h ≤ occurrenceCount π (pattern π S) := by
  have bound := card_le_card_of_injOn (s:=(univ : Finset (Fin h)).powerset)
    (t:=(univ : Finset (Fin n)).powerset.filter (fun T => pattern π T=pattern π S)) choice
    (fun U _ => mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),hp U⟩) inj.injOn
  simpa only [card_powerset,card_univ,Fintype.card_fin,occurrenceCount] using bound

end
end DistinctPermutationPatterns

/-- info: 'DistinctPermutationPatterns.normalizedMean_by_occurrences' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DistinctPermutationPatterns.normalizedMean_by_occurrences

/-- info: 'DistinctPermutationPatterns.local_swap_pattern' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms DistinctPermutationPatterns.local_swap_pattern
