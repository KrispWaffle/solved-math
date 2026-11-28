module

public import SolvedMath.FoldedGraphs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.WellQuasiOrder

@[expose] public section

namespace InducedMinorBands

open SimpleGraph
abbrev Near := FoldedLinearForests.Consecutive

/-- Replace each row of an integer path by an independent set of vertices. -/
def band {W : Type} (row : W → ℕ) : SimpleGraph W where
  Adj x y := Near (row x) (row y)
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun _ h => by rcases h with h | h <;> omega⟩

/-- Disjoint nonempty connected branch sets with exactly the target adjacencies.
    Unused host vertices may be deleted. -/
structure Model {V W : Type} (H : SimpleGraph V) (G : SimpleGraph W) where
  bag : V → Finset W
  inhabited : ∀ i, (bag i).Nonempty
  connected : ∀ i, (G.induce (bag i : Set W)).Connected
  separate : ∀ ⦃i j⦄, i ≠ j → Disjoint (bag i) (bag j)
  edges : ∀ ⦃i j⦄, i ≠ j → (H.Adj i j ↔ ∃ x ∈ bag i, ∃ y ∈ bag j, G.Adj x y)

def IsInducedMinor {V W : Type} (H : SimpleGraph V) (G : SimpleGraph W) := Nonempty (Model H G)

private theorem walk_exit {V : Type} {G : SimpleGraph V} (P : V → Prop) {a b : V}
    (w : G.Walk a b) (ha : P a) (hb : ¬ P b) : ∃ x y, P x ∧ ¬ P y ∧ G.Adj x y := by
  induction w with
  | nil => exact (hb ha).elim
  | @cons a c b e w ih =>
    by_cases hc : P c
    · exact ih hc hb
    · exact ⟨a,c,ha,hc,e⟩

namespace Model

variable {V W : Type} {H : SimpleGraph V} {row : W → ℕ} (M : Model H (band row))

private theorem exit (i : V) (P : W → Prop) {a b : W} (am : a ∈ M.bag i) (bm : b ∈ M.bag i)
    (pa : P a) (pb : ¬ P b) : ∃ x ∈ M.bag i, ∃ y ∈ M.bag i, P x ∧ ¬ P y ∧ Near (row x) (row y) := by
  obtain ⟨w⟩ := M.connected i ⟨a,am⟩ ⟨b,bm⟩
  obtain ⟨x,y,hx,hy,hadj⟩ := walk_exit (fun z => P z.1) w pa pb
  exact ⟨x,x.2,y,y.2,hx,hy,hadj⟩

private def rows (i : V) := (M.bag i).image row

private theorem rows_ne (i : V) : (M.rows i).Nonempty := (M.inhabited i).image row

private def lo (i : V) := (M.rows i).min' (M.rows_ne i)
private def hi (i : V) := (M.rows i).max' (M.rows_ne i)

private theorem bounds {i : V} {x : W} (hx : x ∈ M.bag i) :
    M.lo i ≤ row x ∧ row x ≤ M.hi i := by
  have h := Finset.mem_image_of_mem row hx
  exact ⟨Finset.min'_le _ _ h,Finset.le_max' _ _ h⟩

private theorem ends (i : V) :
    (∃ x ∈ M.bag i, row x = M.lo i) ∧ (∃ y ∈ M.bag i, row y = M.hi i) :=
  ⟨Finset.mem_image.mp (Finset.min'_mem _ _), Finset.mem_image.mp (Finset.max'_mem _ _)⟩

private theorem lo_le_hi (i : V) : M.lo i ≤ M.hi i :=
  (M.rows i).min'_le_max' (M.rows_ne i)

private theorem hit (i : V) (t : ℕ) (hl : M.lo i ≤ t) (hu : t ≤ M.hi i) :
    ∃ x ∈ M.bag i, row x = t := by
  obtain ⟨⟨x,hx,hxl⟩,⟨y,hy,hyh⟩⟩ := M.ends i
  by_cases he : row x = t
  · exact ⟨x,hx,he⟩
  by_cases he' : row y = t
  · exact ⟨y,hy,he'⟩
  obtain ⟨u,_,v,hv,h₁,h₂,hs⟩ := M.exit i (fun z => row z < t) hx hy (by omega) (by omega)
  exact ⟨v,hv,by rcases hs with hs | hs <;> omega⟩

/-- Two anticomplete branch sets meeting the same row cannot leave it. -/
private theorem confined {i j : V} (distinct : i ≠ j) (hn : ¬ H.Adj i j)
    {a b : W} (ha : a ∈ M.bag i) (hb : b ∈ M.bag j) (hab : row a = row b)
    {x : W} (hx : x ∈ M.bag i) : row x = row a := by
  by_contra h
  obtain ⟨u,_,v,hv,hu,_,hs⟩ := M.exit i (fun z => row z = row a) ha hx rfl h
  apply hn ((M.edges distinct).mpr ⟨v,hv,b,hb,?_⟩)
  change Near (row v) (row b)
  rw [← hab,← hu]
  exact Or.symm hs

private theorem hits_between {i j : V} (gap : M.hi i + 1 < M.lo j) {k : V}
    (hik : H.Adj i k) (hjk : H.Adj j k) :
    ∃ z ∈ M.bag k, row z = M.hi i + 1 := by
  obtain ⟨x,hx,v,hv,he⟩ := (M.edges hik.ne).mp hik
  obtain ⟨y,hy,w,hw,he'⟩ := (M.edges hjk.ne).mp hjk
  have bx := M.bounds hx
  have by' := M.bounds hy
  have bv := M.bounds hv
  have bw := M.bounds hw
  change Near (row x) (row v) at he
  change Near (row y) (row w) at he'
  apply M.hit
  · rcases he with he | he <;> omega
  · rcases he' with he' | he' <;> omega

private theorem no_extra_slot {c : ℕ} (slot : W → Fin c)
    (unique : Function.Injective (fun x => (row x,slot x))) (q : Fin (c+1) ↪ V) (t : ℕ)
    (hits : ∀ i, ∃ x ∈ M.bag (q i), row x = t) : False := by
  choose x hx hrow using hits
  have hinj : Function.Injective (fun i => slot (x i)) := by
    intro i j he
    by_contra h
    have e : x i = x j := unique (Prod.ext ((hrow i).trans (hrow j).symm) he)
    exact Finset.disjoint_left.mp (M.separate (q.injective.ne h)) (hx i) (e ▸ hx j)
  have hc := Fintype.card_le_of_injective _ hinj
  simp at hc

/-- Nonadjacent target vertices with more common neighbors than fit in one host row
    must both lie entirely in one row, in every induced-minor model. -/
theorem common_neighbors_force_row {c : ℕ} (slot : W → Fin c)
    (unique : Function.Injective (fun x => (row x,slot x))) {u v : V}
    (distinct : u ≠ v) (nonedge : ¬ H.Adj u v) (q : Fin (c+1) ↪ V)
    (common : ∀ i, H.Adj u (q i) ∧ H.Adj v (q i))
    {x y : W} (hx : x ∈ M.bag u) (hy : y ∈ M.bag v) : row x = row y := by
  classical
  have no_gap {i j : V} (hn : ¬ H.Adj i j) (hd : i ≠ j)
      (co : ∀ k, H.Adj i (q k) ∧ H.Adj j (q k)) : ¬ M.hi i < M.lo j := by
    intro hlt
    by_cases he : M.hi i + 1 = M.lo j
    · obtain ⟨a,ha,har⟩ := (M.ends i).2
      obtain ⟨b,hb,hbr⟩ := (M.ends j).1
      exact hn ((M.edges hd).mpr ⟨a,ha,b,hb,Or.inl (by rw [har,hbr,he])⟩)
    · exact M.no_extra_slot slot unique q _ (fun k =>
        M.hits_between (by omega) (co k).1 (co k).2)
  have h₁ := no_gap nonedge distinct common
  have h₂ := no_gap (fun h => nonedge h.symm) distinct.symm (fun k => (common k).symm)
  let t := max (M.lo u) (M.lo v)
  obtain ⟨a,ha,hra⟩ := M.hit u t (le_max_left _ _) (max_le (M.lo_le_hi _) (by omega))
  obtain ⟨b,hb,hrb⟩ := M.hit v t (le_max_right _ _) (max_le (by omega) (M.lo_le_hi _))
  have he := hra.trans hrb.symm
  have hux := M.confined distinct nonedge ha hb he hx
  have hvy := M.confined distinct.symm (fun h => nonedge h.symm) hb ha he.symm hy
  exact hux.trans (he.trans hvy.symm)

end Model

end InducedMinorBands
