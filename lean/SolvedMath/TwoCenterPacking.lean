module

public import SolvedMath.BipartiteInducedIsomorphism
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

namespace BipartiteInducedIsomorphism

open SimpleGraph

/-- A private leaf names its unique center. A common leaf sees both centers. -/
abbrev Leaf (p : Bool → ℕ) (c : ℕ) := Fin c ⊕ ((s : Bool) × Fin (p s))
abbrev ChairVertex (p : Bool → ℕ) (c : ℕ) := Bool ⊕ Leaf p c

def sees {p c} (s : Bool) : Leaf p c → Prop
  | .inl _ => True
  | .inr i => s = i.1

def chairAdj {p c} : ChairVertex p c → ChairVertex p c → Prop
  | .inl s, .inr l => sees s l
  | .inr l, .inl s => sees s l
  | _, _ => False

def chairs (p : Bool → ℕ) (c : ℕ) : SimpleGraph (ChairVertex p c) where
  Adj := chairAdj
  symm := ⟨by intro a b; cases a <;> cases b <;> exact id⟩
  loopless := ⟨by intro a; cases a <;> exact id⟩

def star (k : ℕ) : SimpleGraph (Option (Fin k)) where
  Adj u v := u.isSome ≠ v.isSome
  symm := ⟨fun _ _ => Ne.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

abbrev ForestVertex {I : Type} (w : I → ℕ) := (i : I) × Option (Fin (w i))

def forest {I : Type} (w : I → ℕ) : SimpleGraph (ForestVertex w) where
  Adj u v := u.1 = v.1 ∧ u.2.isSome ≠ v.2.isSome
  symm := ⟨fun _ _ h => ⟨h.1.symm, Ne.symm h.2⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

def starInForest {I : Type} (w : I → ℕ) (i : I) : star (w i) ↪g forest w where
  toFun v := ⟨i,v⟩
  inj' _ _ h := by simpa using h
  map_rel_iff' := by intro a b; exact ⟨And.right, fun h => ⟨rfl,h⟩⟩

def privateLeaf {p c} (s : Bool) (i : Fin (p s)) : ChairVertex p c :=
  .inr (.inr ⟨s,i⟩)

def neighbor {p c} (s : Bool) : Fin c ⊕ Fin (p s) → ChairVertex p c
  | .inl i => .inr (.inl i)
  | .inr i => privateLeaf s i

theorem neighbor_injective {p c} (s : Bool) : Function.Injective (@neighbor p c s) := by
  rintro (i | i) (j | j) h <;> simp [neighbor, privateLeaf] at h ⊢ <;> exact h

theorem adjacent_center {p c} {s : Bool} {v : ChairVertex p c} :
    (chairs p c).Adj (.inl s) v ↔ ∃ i, neighbor s i = v := by
  cases v with
  | inl a =>
    constructor
    · exact False.elim
    · rintro ⟨i, hi⟩; cases i <;> cases hi
  | inr l =>
    cases l with
    | inl a => exact ⟨fun _ => ⟨.inl a, rfl⟩, fun _ => trivial⟩
    | inr i =>
      rcases i with ⟨t,j⟩
      constructor
      · rintro (rfl : s = t); exact ⟨.inr j, rfl⟩
      · rintro ⟨a | a,h⟩
        · cases h
        · cases h; rfl

theorem adjacent_only {p c} {s : Bool} {v : ChairVertex p c} :
    (chairs p c).Adj (.inl s) v ∧ ¬ (chairs p c).Adj (.inl (!s)) v ↔
      ∃ i, privateLeaf s i = v := by
  constructor
  · rintro ⟨hs,hn⟩
    obtain ⟨i | i,rfl⟩ := adjacent_center.mp hs
    · exact (hn trivial).elim
    · exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨rfl, by change ¬ (!s) = s; cases s <;> decide⟩

/-- The center of any embedded star with at least three leaves maps to a chair. -/
theorem star_center {k p c} (hk : 3 ≤ k) (f : star k ↪g chairs p c) :
    ∃ s : Bool, f none = .inl s := by
  cases h : f none with
  | inl s => exact ⟨s,rfl⟩
  | inr l =>
    have hchair (i : Fin k) : ∃ s : Bool, f (some i) = .inl s := by
      have h' : (chairs p c).Adj (f none) (f (some i)) :=
        f.map_rel_iff.mpr Bool.false_ne_true
      rw [h] at h'
      cases e : f (some i) with
      | inl s => exact ⟨s,rfl⟩
      | inr q => rw [e] at h'; exact False.elim h'
    choose seat hseat using hchair
    have hinj : Function.Injective seat := by
      intro i j heq
      exact Option.some.inj (f.injective ((hseat i).trans ((congrArg Sum.inl heq).trans (hseat j).symm)))
    have hcard := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin, Fintype.card_bool] at hcard
    omega

theorem star_bound_at {k p c} (f : star k ↪g chairs p c) {s : Bool}
    (hs : f none = .inl s) : k ≤ c + p s := by
  have h (i : Fin k) : ∃ j, neighbor s j = f (some i) := by
    apply adjacent_center.mp
    rw [← hs]
    exact f.map_rel_iff.mpr Bool.false_ne_true
  choose g hg using h
  have hgi : Function.Injective g := by
    intro i j eq
    exact Option.some.inj (f.injective ((hg i).symm.trans ((congrArg (neighbor s) eq).trans (hg j))))
  simpa using Fintype.card_le_of_injective _ hgi

def starAt {k p c} (s : Bool) (g : Fin k ↪ Fin c ⊕ Fin (p s)) : star k ↪g chairs p c where
  toFun
    | none => .inl s
    | some i => neighbor s (g i)
  inj' := by
    rintro (_ | i) (_ | j) h
    · rfl
    · cases e : g j <;> simp [e, neighbor, privateLeaf] at h
    · cases e : g i <;> simp [e, neighbor, privateLeaf] at h
    · exact congrArg some (g.injective (neighbor_injective s h))
  map_rel_iff' := by
    rintro (_ | i) (_ | j)
    · change False ↔ false ≠ false; simp
    · exact ⟨fun _ => Bool.false_ne_true, fun _ => adjacent_center.mpr ⟨_,rfl⟩⟩
    · exact ⟨fun _ => Ne.symm Bool.false_ne_true, fun _ => (chairs p c).adj_symm (adjacent_center.mpr ⟨_,rfl⟩)⟩
    · change (chairs p c).Adj (neighbor s (g i)) (neighbor s (g j)) ↔ true ≠ true
      cases g i <;> cases g j <;> simp [neighbor, privateLeaf, chairs, chairAdj]

theorem star_fits {k p c} (hk : 3 ≤ k) :
    Nonempty (star k ↪g chairs p c) ↔ ∃ s, k ≤ c + p s := by
  constructor
  · rintro ⟨f⟩; obtain ⟨s,hs⟩ := star_center hk f
    exact ⟨s, star_bound_at f hs⟩
  · rintro ⟨s,hs⟩
    have hc : Fintype.card (Fin k) ≤ Fintype.card (Fin c ⊕ Fin (p s)) := by simpa
    obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hc
    exact ⟨starAt s g⟩

/-- An uncolored embedding of a star forest still chooses different chairs for all its centers. -/
theorem forest_centers {I : Type} {w : I → ℕ} {p c} (hw : ∀ i, 3 ≤ w i)
    (f : forest w ↪g chairs p c) :
    ∃ g : I ↪ Bool, ∀ i, f ⟨i,none⟩ = .inl (g i) := by
  have h (i : I) : ∃ s : Bool, f ⟨i,none⟩ = .inl s :=
    star_center (hw i) ((starInForest w i).trans f)
  choose g hg using h
  refine ⟨⟨g, ?_⟩,hg⟩
  intro i j he
  exact congrArg Sigma.fst (f.injective ((hg i).trans ((congrArg Sum.inl he).trans (hg j).symm)))

theorem two_private_bounds {I : Type} {w : I → ℕ} {p c}
    (f : forest w ↪g chairs p c) {i j : I} (hij : i ≠ j) {s : Bool}
    (hi : f ⟨i,none⟩ = .inl s) (hj : f ⟨j,none⟩ = .inl (!s)) : w i ≤ p s := by
  have h (k : Fin (w i)) : ∃ z, privateLeaf s z = f ⟨i,some k⟩ := by
    apply adjacent_only.mp
    rw [← hi, ← hj]
    constructor
    · exact f.map_rel_iff.mpr ⟨rfl, Bool.false_ne_true⟩
    · intro adj; exact hij (f.map_rel_iff.mp adj).1.symm
  choose g hg using h
  have hgi : Function.Injective g := by
    intro k l eq
    have hh := f.injective ((hg k).symm.trans ((congrArg (privateLeaf s) eq).trans (hg l)))
    simpa using hh
  simpa using Fintype.card_le_of_injective _ hgi

private def seatOf {p c} : ChairVertex p c → Bool
  | .inl s => s
  | .inr (.inl _) => false
  | .inr (.inr i) => i.1

def plant {I : Type} {w : I → ℕ} {p : Bool → ℕ} (c : ℕ) (g : I ↪ Bool)
    (space : ∀ i, w i ≤ p (g i)) : ForestVertex w → ChairVertex p c
  | ⟨i,none⟩ => .inl (g i)
  | ⟨i,some k⟩ => privateLeaf (g i) (k.castLE (space i))

/-- Install a family of stars on distinct centers using only private leaves. -/
def privatePlacement {I : Type} {w : I → ℕ} {p : Bool → ℕ} (c : ℕ) (g : I ↪ Bool)
    (space : ∀ i, w i ≤ p (g i)) : forest w ↪g chairs p c where
  toFun := plant c g space
  inj' := by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have hi : i = j := by
      apply g.injective
      have hs := congrArg seatOf h
      cases x <;> cases y <;> exact hs
    subst j
    cases x <;> cases y <;> simp_all [plant, privateLeaf, Fin.ext_iff]
  map_rel_iff' := by
    rintro ⟨i,x⟩ ⟨j,y⟩
    change chairAdj (plant c g space ⟨i,x⟩) (plant c g space ⟨j,y⟩) ↔
      i = j ∧ x.isSome ≠ y.isSome
    cases x <;> cases y <;> simp [plant, privateLeaf, chairAdj, sees, eq_comm]

/-- Exact induced packing criterion for two ordinary stars, including both possible orientations. -/
theorem two_stars_fit {w : Bool → ℕ} {p c} (hw : ∀ i, 3 ≤ w i) :
    Nonempty (forest w ↪g chairs p c) ↔
    ∃ g : Bool ↪ Bool, ∀ i, w i ≤ p (g i) := by
  constructor
  · rintro ⟨f⟩
    obtain ⟨g,hg⟩ := forest_centers hw f
    refine ⟨g, fun i => ?_⟩
    have hne : i ≠ !i := by cases i <;> decide
    have hflip : g (!i) = !(g i) := by
      have hn := fun h => hne (g.injective h)
      cases a : g i <;> cases b : g (!i) <;> simp_all
    exact two_private_bounds f hne (hg i) ((hg (!i)).trans (congrArg Sum.inl hflip))
  · rintro ⟨g,hg⟩
    exact ⟨privatePlacement c g hg⟩

/-- The adjustment to the number of common leaves makes the maximum degree a sum. -/
theorem blocker_fits {h q a b : ℕ} (hk : 3 ≤ h + q) :
    Nonempty (star (h+q) ↪g chairs (fun s => if s then b else a) (h + min a b)) ↔
      q ≤ a+b := by
  rw [star_fits hk]
  constructor
  · rintro ⟨s,hs⟩
    cases s <;> simp at hs <;> omega
  · intro hq
    by_cases hle : a ≤ b
    · exact ⟨true, by simp [Nat.min_eq_left hle]; omega⟩
    · exact ⟨false, by simp [Nat.min_eq_right (by omega : b ≤ a)]; omega⟩

theorem path_six_free (p : Bool → ℕ) (c : ℕ) : IsEmpty (pathGraph 6 ↪g chairs p c) := by
  refine ⟨fun f => ?_⟩
  let left (i : Fin 3) : Fin 6 := ⟨2 * i.val, by omega⟩
  let right (i : Fin 3) : Fin 6 := ⟨2 * i.val + 1, by omega⟩
  have edge (i : Fin 3) : (chairs p c).Adj (f (left i)) (f (right i)) :=
    f.map_rel_iff.mpr (Or.inl rfl)
  have hit (i : Fin 3) : ∃ s : Bool, ∃ k : Fin 6,
      (k = left i ∨ k = right i) ∧ f k = .inl s := by
    cases e : f (left i) with
    | inl s => exact ⟨s,left i,Or.inl rfl,e⟩
    | inr l =>
      cases d : f (right i) with
      | inl s => exact ⟨s,right i,Or.inr rfl,d⟩
      | inr z =>
        have hd := edge i
        rw [e,d] at hd
        exact False.elim hd
  choose seat vert place coord using hit
  have inj : Function.Injective seat := by
    intro i j he
    have eq := congrArg Fin.val (f.injective ((coord i).trans ((congrArg Sum.inl he).trans (coord j).symm)))
    apply Fin.ext
    rcases place i with h | h <;> rcases place j with g | g <;> rw [h,g] at eq <;>
      simp only [left,right] at eq <;> omega
  have := Fintype.card_le_of_injective _ inj
  simp at this

end BipartiteInducedIsomorphism
