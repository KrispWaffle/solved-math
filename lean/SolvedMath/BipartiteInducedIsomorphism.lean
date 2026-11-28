module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace BipartiteInducedIsomorphism

open SimpleGraph

/-- A row consists of its suffix flag, interval endpoint and copy number. -/
abbrev Row (t : ℕ) := Bool × Fin t × Fin t
abbrev BinVertex (t : ℕ) := Fin t ⊕ Row t

def hits {t} (r : Row t) (v : Fin t) : Prop :=
  if r.1 then r.2.1 ≤ v else v ≤ r.2.1

def binAdj {t} : BinVertex t → BinVertex t → Prop
  | .inl v, .inr r => hits r v
  | .inr r, .inl v => hits r v
  | _, _ => False

def bin (t : ℕ) : SimpleGraph (BinVertex t) where
  Adj := binAdj
  symm := ⟨by intro u v; cases u <;> cases v <;> exact id⟩
  loopless := ⟨by intro u; cases u <;> exact id⟩

abbrev ItemVertex {I : Type} (w : I → ℕ) := (i : I) × Bool × Fin (w i)

/-- A disjoint union of balanced complete bipartite graphs. -/
def items {I : Type} (w : I → ℕ) : SimpleGraph (ItemVertex w) where
  Adj u v := u.1 = v.1 ∧ u.2.1 ≠ v.2.1
  symm := ⟨fun _ _ h => ⟨h.1.symm, Ne.symm h.2⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

private theorem edge_column {t : ℕ} {u v : BinVertex t} (h : (bin t).Adj u v) :
    ∃ c : Fin t, u = .inl c ∨ v = .inl c := by
  cases u with
  | inl c => exact ⟨c, Or.inl rfl⟩
  | inr r =>
    cases v with
    | inl c => exact ⟨c, Or.inr rfl⟩
    | inr s => exact False.elim h

/-- Every vertex-disjoint edge spends a different column, for either source coloring. -/
theorem column_injection {I : Type} {w : I → ℕ} {t : ℕ} (f : items w ↪g bin t) :
    Nonempty (((i : I) × Fin (w i)) ↪ Fin t) := by
  classical
  let endpoint (s : (i : I) × Fin (w i)) (color : Bool) : ItemVertex w :=
    ⟨s.1, color, s.2⟩
  have h (s : (i : I) × Fin (w i)) :
      ∃ c : Fin t, ∃ color : Bool, f (endpoint s color) = .inl c := by
    have adj : (items w).Adj (endpoint s false) (endpoint s true) := ⟨rfl, Bool.false_ne_true⟩
    obtain ⟨c, hc | hc⟩ := edge_column (f.map_rel_iff.mpr adj)
    · exact ⟨c, false, hc⟩
    · exact ⟨c, true, hc⟩
  choose column color witness using h
  refine ⟨⟨column, ?_⟩⟩
  intro a b hab
  have eq := f.injective ((witness a).trans ((congrArg Sum.inl hab).trans (witness b).symm))
  exact congrArg (fun q : ItemVertex w => (⟨q.1, q.2.2⟩ : (i : I) × Fin (w i))) eq

theorem capacity {I : Type} [Fintype I] {w : I → ℕ} {t : ℕ}
    (f : items w ↪g bin t) : ∑ i, w i ≤ t := by
  obtain ⟨g⟩ := column_injection f
  simpa using Fintype.card_le_of_embedding g

theorem private_rows {t : ℕ} {r s : Row t} {u v : Fin t}
    (hr : hits r u) (hs : hits s v) (hrv : ¬ hits r v) (hsu : ¬ hits s u) :
    r.1 ≠ s.1 := by
  rcases r with ⟨b, i, j⟩
  rcases s with ⟨d, k, l⟩
  cases b <;> cases d <;> simp_all [hits] <;> omega

/-- An identity adjacency submatrix on three edges cannot occur in a bin. -/
theorem no_three_private {t : ℕ} (r : Fin 3 → Row t) (v : Fin 3 → Fin t)
    (h : ∀ i j, hits (r i) (v j) ↔ i = j) : False := by
  have distinct : Function.Injective (fun i => (r i).1) := by
    intro i j eq
    by_contra ne
    exact private_rows ((h i i).mpr rfl) ((h j j).mpr rfl)
      (fun hij => ne ((h i j).mp hij)) (fun hji => ne ((h j i).mp hji).symm) eq
  have := Fintype.card_le_of_injective _ distinct
  simp at this

theorem edge_row_column {t} {u v : BinVertex t} (h : (bin t).Adj u v) :
    ∃ r c, hits r c ∧ (Sum.inr r = u ∨ Sum.inr r = v) ∧
      (Sum.inl c = u ∨ Sum.inl c = v) := by
  cases u <;> cases v
  · exact False.elim h
  · exact ⟨_, _, h, Or.inr rfl, Or.inl rfl⟩
  · exact ⟨_, _, h, Or.inl rfl, Or.inr rfl⟩
  · exact False.elim h

theorem no_induced_three_edges {t} (a b : Fin 3 → BinVertex t)
    (edge : ∀ i, (bin t).Adj (a i) (b i))
    (cross : ∀ i j, i ≠ j → ∀ u v, (u = a i ∨ u = b i) →
      (v = a j ∨ v = b j) → ¬ (bin t).Adj u v) : False := by
  choose r c hit row col using fun i => edge_row_column (edge i)
  apply no_three_private r c
  intro i j
  constructor
  · intro h
    by_contra ne
    exact cross i j ne _ _ (row i) (col j) h
  · rintro rfl
    exact hit i

def pathGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i.val + 1 = j.val ∨ j.val + 1 = i.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with h | h <;> omega⟩

/-- Edges 01, 34 and 67 of the eight-vertex path form an induced matching. -/
theorem path_eight_free (t : ℕ) : IsEmpty (pathGraph 8 ↪g bin t) := by
  refine ⟨fun f => ?_⟩
  let l (i : Fin 3) : Fin 8 := ⟨3 * i.val, by omega⟩
  let r (i : Fin 3) : Fin 8 := ⟨3 * i.val + 1, by omega⟩
  apply no_induced_three_edges (fun i => f (l i)) (fun i => f (r i))
  · intro i
    exact f.map_rel_iff.mpr (Or.inl rfl)
  · intro i j h u v hu hv
    have hij : i.val ≠ j.val := fun eq => h (Fin.ext eq)
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> intro adj <;>
      obtain hp | hp := f.map_rel_iff.mp adj <;>
      simp only [l, r] at hp <;> omega

end BipartiteInducedIsomorphism
