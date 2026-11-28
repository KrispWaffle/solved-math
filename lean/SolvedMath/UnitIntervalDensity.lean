module

public import SolvedMath.UnitIntervalTracks
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

namespace UnitIntervalMinors

open Set
open InducedMinorBands (IsInducedMinor)

theorem overlap_iff {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (Icc a b ∩ Icc c d).Nonempty ↔ a ≤ d ∧ c ≤ b := by
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨hx.1.trans hy.2, hy.1.trans hx.2⟩
  · rintro ⟨had,hcb⟩
    exact ⟨max a c, ⟨le_max_left _ _, max_le hab hcb⟩, ⟨le_max_right _ _,max_le had hcd⟩⟩

private noncomputable def rank (S : Finset ℝ) (x : ℝ) := (S.filter (· ≤ x)).card

private theorem rank_mono (S : Finset ℝ) : Monotone (rank S) := by
  intro a b hab
  exact Finset.card_le_card fun _ hi => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2.trans hab⟩

private theorem rank_lt {S : Finset ℝ} {a b : ℝ} (hb : b ∈ S) (hab : a < b) :
    rank S a < rank S b := by
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset
    (fun _ hi => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,(Finset.mem_filter.mp hi).2.trans hab.le⟩)).mpr
  exact ⟨b,Finset.mem_filter.mpr ⟨hb,le_rfl⟩,fun ha => hab.not_ge (Finset.mem_filter.mp ha).2⟩

/-- Every interval graph on h vertices is present in every sorted unit representation
    of coverage at least h on a segment of length 6h, even when target endpoints coincide. -/
theorem long_dense_segment {n h : ℕ} (start : Fin n → ℝ) (mono : Monotone start)
    (left right : Fin h → ℝ) (ends : ∀ i, left i ≤ right i) (a b : ℝ)
    (length : a + 6*h ≤ b)
    (height : ∀ x ∈ Icc a b,
      h ≤ (Finset.univ.filter fun i => x ∈ Icc (start i) (start i+1)).card) :
    IsInducedMinor (intervalGraph left right) (unitGraph start) := by
  classical
  let S := Finset.univ.image left ∪ Finset.univ.image right
  have lmem (i) : left i ∈ S := Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have rmem (i) : right i ∈ S := Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have card : S.card ≤ h + h := by
    calc
      S.card ≤ (Finset.univ.image left).card + (Finset.univ.image right).card := Finset.card_union_le _ _
      _ ≤ _ := by
        simpa using Nat.add_le_add (Finset.card_image_le (s := Finset.univ) (f := left))
          (Finset.card_image_le (s := Finset.univ) (f := right))
  let stretch (x : ℝ) := a + 3*(rank S x : ℝ)
  have smono : Monotone stretch := fun _ _ hxy => by
    dsimp [stretch]
    gcongr
    exact rank_mono S hxy
  have reflects {x y : ℝ} (hx : x ∈ S) : stretch x ≤ stretch y ↔ x ≤ y := by
    refine ⟨fun hab => ?_,fun hxy => smono hxy⟩
    by_contra! hyx
    have hreal : (rank S y : ℝ) < rank S x := by exact_mod_cast rank_lt hx hyx
    dsimp [stretch] at hab
    linarith
  have stretchedEnds (i) : stretch (left i) ≤ stretch (right i) := smono (ends i)
  have same : intervalGraph left right = intervalGraph (stretch ∘ left) (stretch ∘ right) := by
    ext i j
    change (_ ∧ _) ↔ (_ ∧ _)
    simp only [Function.comp_apply]
    rw [overlap_iff (ends i) (ends j),overlap_iff (stretchedEnds i) (stretchedEnds j)]
    simp only [reflects (lmem _)]
  rw [same]
  apply dense_segment_model start mono (stretch ∘ left) (stretch ∘ right) stretchedEnds a b _ _ height
  · intro i
    have count : rank S (right i) ≤ h+h := (Finset.card_le_card (Finset.filter_subset _ _)).trans card
    have cr : (rank S (right i) : ℝ) ≤ (h : ℝ)+h := by exact_mod_cast count
    dsimp [stretch]
    constructor
    · have nonneg : 0 ≤ (rank S (left i) : ℝ) := by positivity
      linarith
    · linarith
  · intro i j sep
    change stretch (right i) < stretch (left j) at sep
    have ri : rank S (right i) < rank S (left j) := by
      by_contra! con
      have cr : (rank S (left j) : ℝ) ≤ rank S (right i) := by exact_mod_cast con
      dsimp [stretch] at sep
      linarith
    have cr : (rank S (right i) : ℝ)+1 ≤ rank S (left j) := by exact_mod_cast ri
    dsimp [stretch]
    linarith

/-- The ordered host has h identical unit intervals starting at each integer from zero to 6h. -/
def gridStart (h : ℕ) (i : Fin ((6*h+1)*h)) : ℝ := (i.val/h : ℕ)

theorem interval_graph_in_unit_grid {h : ℕ} (left right : Fin h → ℝ)
    (ends : ∀ i, left i ≤ right i) :
    IsInducedMinor (intervalGraph left right) (unitGraph (gridStart h)) := by
  classical
  apply long_dense_segment (gridStart h) (fun x y hxy => ?_) left right ends 0 (6*h) (by simp)
  · intro x hx
    by_cases hz : h = 0
    · simp [hz]
    have hp := Nat.pos_of_ne_zero hz
    let k := ⌊x⌋₊
    have low : (k : ℝ) ≤ x := Nat.floor_le hx.1
    have upper : x ≤ (k : ℝ)+1 := (Nat.lt_floor_add_one x).le
    have kk : k ≤ 6*h := by exact_mod_cast (low.trans hx.2 : (k : ℝ) ≤ 6*(h : ℝ))
    let vertex (c : Fin h) : Fin ((6*h+1)*h) :=
      ⟨k*h + c.val, by
        calc
          k*h+c.val < k*h+h := Nat.add_lt_add_left c.isLt _
          _ ≤ (6*h+1)*h := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)⟩
    have inj : Function.Injective vertex := fun c d he => Fin.ext (by
      have := congrArg Fin.val he
      dsimp [vertex] at this
      omega)
    have sub : Finset.univ.image vertex ⊆
        Finset.univ.filter (fun i => x ∈ Icc (gridStart h i) (gridStart h i+1)) := by
      intro i hi
      obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hi
      have vstart : gridStart h (vertex c) = k := by
        change (((k*h+c.val)/h : ℕ) : ℝ) = k
        rw [Nat.mul_comm k h, Nat.mul_add_div hp, Nat.div_eq_of_lt c.isLt, Nat.add_zero]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,vstart ▸ ⟨low,upper⟩⟩
    simpa [Finset.card_image_of_injective _ inj] using Finset.card_le_card sub
  · change ((x.val/h : ℕ) : ℝ) ≤ ((y.val/h : ℕ) : ℝ)
    exact_mod_cast Nat.div_le_div_right hxy

end UnitIntervalMinors
