module

public import SolvedMath.TwoCenterPacking
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace BipartiteInducedIsomorphism

open SimpleGraph

def disjointGraph {J : Type} {V : J → Type} (g : ∀ j, SimpleGraph (V j)) :
    SimpleGraph ((j : J) × V j) where
  Adj u v := ∃ h : u.1 = v.1, (g v.1).Adj (h ▸ u.2) v.2
  symm := ⟨by rintro ⟨i,u⟩ ⟨j,v⟩ ⟨h,adj⟩; cases h; exact ⟨rfl,(g i).adj_symm adj⟩⟩
  loopless := ⟨by rintro ⟨i,u⟩ ⟨h,adj⟩; exact (g i).loopless.irrefl _ adj⟩

@[simp] theorem adj_at {J : Type} {V : J → Type} {g : ∀ j, SimpleGraph (V j)}
    {j : J} {u v : V j} :
    (disjointGraph g).Adj ⟨j,u⟩ ⟨j,v⟩ ↔ (g j).Adj u v :=
  ⟨fun h => h.elim fun _ adj => adj, fun h => ⟨rfl,h⟩⟩

def pieceAt {J : Type} {V : J → Type} {j : J} (u : (j : J) × V j) (h : u.1 = j) : V j :=
  h ▸ u.2

@[simp] theorem pieceAt_mk {J : Type} {V : J → Type} {j : J} (u : (j : J) × V j)
    (h : u.1 = j) : (⟨j,pieceAt u h⟩ : (j : J) × V j) = u := by
  rcases u with ⟨k,u⟩
  cases h
  rfl

abbrev FiberWeight {I J : Type} (w : I → ℕ) (assign : I → J) (j : J)
    (i : {i // assign i = j}) := w i.val

def forgetBin {I J : Type} {w : I → ℕ} {a : I → J} {j : J}
    (u : ForestVertex (FiberWeight w a j)) : ForestVertex w := ⟨u.1.val,u.2⟩

theorem forgetBin_injective {I J : Type} {w : I → ℕ} {a : I → J} {j : J} :
    Function.Injective (@forgetBin I J w a j) := by
  rintro ⟨⟨i,hi⟩,u⟩ ⟨⟨k,hk⟩,v⟩ h
  cases h
  rfl

@[simp] theorem forgetBin_adj {I J : Type} {w : I → ℕ} {a : I → J} {j : J}
    (u v : ForestVertex (FiberWeight w a j)) :
    (forest w).Adj (forgetBin u) (forgetBin v) ↔ (forest (FiberWeight w a j)).Adj u v := by
  exact and_congr_left (fun _ => Subtype.ext_iff.symm)

def centerBin {I J : Type} {w : I → ℕ} {V : J → Type} {g : ∀ j, SimpleGraph (V j)}
    (f : forest w ↪g disjointGraph g) (i : I) : J := (f ⟨i,none⟩).1

theorem assigned_part {I J : Type} {w : I → ℕ} {V : J → Type} {g : ∀ j, SimpleGraph (V j)}
    (f : forest w ↪g disjointGraph g) (i : I) (u : Option (Fin (w i))) :
    (f ⟨i,u⟩).1 = centerBin f i := by
  cases u with
  | none => rfl
  | some k =>
    have adj : (forest w).Adj ⟨i,some k⟩ ⟨i,none⟩ := ⟨rfl,Ne.symm Bool.false_ne_true⟩
    exact (f.map_rel_iff.mpr adj).elim (fun h _ => h)

def restrictToBin {I J : Type} {w : I → ℕ} {V : J → Type} {g : ∀ j, SimpleGraph (V j)}
    (f : forest w ↪g disjointGraph g) (j : J) :
    forest (FiberWeight w (centerBin f) j) ↪g g j := by
  let h (u : ForestVertex (FiberWeight w (centerBin f) j)) :
      (f (forgetBin u)).1 = j := (assigned_part f u.1.val u.2).trans u.1.property
  let part (u : ForestVertex (FiberWeight w (centerBin f) j)) := pieceAt (f (forgetBin u)) (h u)
  have repr (u) : (⟨j,part u⟩ : (j : J) × V j) = f (forgetBin u) := pieceAt_mk _ _
  refine ⟨⟨part,?_⟩,?_⟩
  · intro u v eq
    exact forgetBin_injective (f.injective ((repr u).symm.trans ((congrArg (Sigma.mk j) eq).trans (repr v))))
  · intro u v
    change (g j).Adj (part u) (part v) ↔ _
    rw [← adj_at (g := g), repr, repr, f.map_rel_iff, forgetBin_adj]

def assignedVertex {I J : Type} {w : I → ℕ} (a : I → J) (v : ForestVertex w) :
    ForestVertex (FiberWeight w a (a v.1)) := ⟨⟨v.1,rfl⟩,v.2⟩

def placeAll {I J : Type} {w : I → ℕ} {V : J → Type} {g : ∀ j, SimpleGraph (V j)}
    (a : I → J) (localMap : ∀ j, forest (FiberWeight w a j) ↪g g j) :
    forest w ↪g disjointGraph g := by
  let place (v : ForestVertex w) : (j : J) × V j := ⟨a v.1,localMap _ (assignedVertex a v)⟩
  have repr (j) (v : ForestVertex (FiberWeight w a j)) :
      place (forgetBin v) = ⟨j,localMap j v⟩ := by
    rcases v with ⟨⟨i,hi⟩,v⟩
    cases hi
    rfl
  refine ⟨⟨place,?_⟩,?_⟩
  · intro u v eq
    have he : a v.1 = a u.1 := (congrArg Sigma.fst eq).symm
    let u' : ForestVertex (FiberWeight w a (a u.1)) := ⟨⟨u.1,rfl⟩,u.2⟩
    let v' : ForestVertex (FiberWeight w a (a u.1)) := ⟨⟨v.1,he⟩,v.2⟩
    change place (forgetBin u') = place (forgetBin v') at eq
    rw [repr,repr] at eq
    exact congrArg forgetBin ((localMap _).injective (sigma_mk_injective eq))
  · intro u v
    change (disjointGraph g).Adj (place u) (place v) ↔ _
    by_cases he : a v.1 = a u.1
    · let u' : ForestVertex (FiberWeight w a (a u.1)) := ⟨⟨u.1,rfl⟩,u.2⟩
      let v' : ForestVertex (FiberWeight w a (a u.1)) := ⟨⟨v.1,he⟩,v.2⟩
      change (disjointGraph g).Adj (place (forgetBin u')) (place (forgetBin v')) ↔
        (forest w).Adj (forgetBin u') (forgetBin v')
      rw [repr,repr,adj_at,(localMap _).map_rel_iff,forgetBin_adj]
    · constructor
      · rintro ⟨eq,_⟩; exact (he eq.symm).elim
      · intro h; exact (he (congrArg a h.1.symm)).elim

/-- Literal induced embeddings of the whole forest are precisely feasible assignments
    of its stars to host components. Both directions apply to uncolored embeddings. -/
theorem forest_packing_iff {I J : Type} {w : I → ℕ} {V : J → Type} {g : ∀ j, SimpleGraph (V j)} :
    Nonempty (forest w ↪g disjointGraph g) ↔
    ∃ a : I → J, ∀ j, Nonempty (forest (FiberWeight w a j) ↪g g j) := by
  constructor
  · rintro ⟨f⟩
    exact ⟨centerBin f, fun j => ⟨restrictToBin f j⟩⟩
  · rintro ⟨a,ha⟩
    classical
    exact ⟨placeAll a (fun j => (ha j).some)⟩

theorem saturation {J : Type} [Fintype J] {load supply : J → ℕ}
    (le : ∀ j, load j ≤ supply j) (total : ∑ j, load j = ∑ j, supply j) :
    ∀ j, load j = supply j := by
  intro j
  by_contra h
  have strict := Finset.sum_lt_sum (fun i (_ : i ∈ (Finset.univ : Finset J)) => le i)
    ⟨j,Finset.mem_univ j,lt_of_le_of_ne (le j) h⟩
  omega

def uniqueStar {I : Type} {w : I → ℕ} (i : I) (only : ∀ j, j = i) :
    forest w ↪g star (w i) := by
  let get (v : ForestVertex w) : Option (Fin (w i)) := only v.1 ▸ v.2
  have undo (v : ForestVertex w) : (⟨i,get v⟩ : ForestVertex w) = v := by
    rcases v with ⟨j,v⟩
    obtain rfl := only j
    rfl
  refine ⟨⟨get,?_⟩,?_⟩
  · intro u v h
    exact (undo u).symm.trans ((congrArg (Sigma.mk i) h).trans (undo v))
  · intro u v
    change (star (w i)).Adj (get u) (get v) ↔ (forest w).Adj u v
    conv_rhs => rw [← undo u, ← undo v]
    exact ⟨fun h => ⟨rfl,h⟩,And.right⟩

/-- A bin may use its common leaves for a single star, or use just its private leaves
    for stars at distinct centers. This predicate has no graph embeddings in it. -/
def BinFeasible {I : Type} (w : I → ℕ) (p : Bool → ℕ) (c : ℕ) : Prop :=
  (∃ g : I ↪ Bool, ∀ i, w i ≤ p (g i)) ∨
  (∃ i : I, (∀ j, j = i) ∧ ∃ s, w i ≤ c + p s)

theorem bin_feasible_iff {I : Type} {w : I → ℕ} {p c} (hw : ∀ i, 3 ≤ w i) :
    Nonempty (forest w ↪g chairs p c) ↔ BinFeasible w p c := by
  classical
  constructor
  · rintro ⟨f⟩
    by_cases h : ∃ i : I, ∀ j, j = i
    · obtain ⟨i,hi⟩ := h
      exact Or.inr ⟨i,hi,(star_fits (hw i)).mp ⟨(starInForest w i).trans f⟩⟩
    · obtain ⟨g,hg⟩ := forest_centers hw f
      apply Or.inl
      refine ⟨g, fun i => ?_⟩
      obtain ⟨j,hj⟩ : ∃ j, j ≠ i := by
        by_contra! no
        exact h ⟨i,no⟩
      have diff : g j ≠ g i := fun eq => hj (g.injective eq)
      have flip : g j = !(g i) := by cases e : g i <;> cases d : g j <;> simp_all
      exact two_private_bounds f hj.symm (hg i) ((hg j).trans (congrArg Sum.inl flip))
  · rintro (⟨g,hg⟩ | ⟨i,hi,hs⟩)
    · exact ⟨privatePlacement c g hg⟩
    · obtain ⟨f⟩ := (star_fits (hw i)).mpr hs
      exact ⟨(uniqueStar i hi).trans f⟩

/-- A graph-level criterion for a whole star forest and disjoint two-center components. -/
theorem packing_by_capacities {I J : Type} (w : I → ℕ) (p : J → Bool → ℕ) (c : J → ℕ)
    (hw : ∀ i, 3 ≤ w i) :
    Nonempty (forest w ↪g disjointGraph (fun j => chairs (p j) (c j))) ↔
      ∃ a : I → J, ∀ j, BinFeasible (FiberWeight w a j) (p j) (c j) := by
  rw [forest_packing_iff]
  apply exists_congr
  intro a
  apply forall_congr'
  intro j
  exact bin_feasible_iff (fun i => hw i.val)

end BipartiteInducedIsomorphism
