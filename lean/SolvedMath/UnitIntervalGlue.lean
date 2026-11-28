module

public import SolvedMath.UnitIntervalTracks
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

@[expose] public section

namespace UnitIntervalMinors

open SimpleGraph
open InducedMinorBands (Model IsInducedMinor)

/-- A model on specified sets of vertices of ambient graphs, with empty branches outside
    the source set. Keeping ambient names allows a port to belong to both adjacent pieces. -/
structure SlabModel {V W : Type} (H : SimpleGraph V) (G : SimpleGraph W)
    (s : Finset V) (t : Finset W) where
  bag : V → Finset W
  present : ∀ i, (bag i).Nonempty ↔ i ∈ s
  within : ∀ i, bag i ⊆ t
  connected : ∀ i ∈ s, (G.induce (bag i : Set W)).Connected
  separate : ∀ ⦃i j⦄, i ≠ j → Disjoint (bag i) (bag j)
  edges : ∀ ⦃i j⦄, i ≠ j → ((i ∈ s ∧ j ∈ s ∧ H.Adj i j) ↔
    ∃ x ∈ bag i, ∃ y ∈ bag j, G.Adj x y)

/-- Every edge of the union has both ends in one piece. -/
def EdgesCovered {V : Type} [DecidableEq V] (G : SimpleGraph V) (s t : Finset V) :=
  ∀ ⦃x⦄, x ∈ s ∪ t → ∀ ⦃y⦄, y ∈ s ∪ t → G.Adj x y →
    (x ∈ s ∧ y ∈ s) ∨ (x ∈ t ∧ y ∈ t)

namespace SlabModel

variable {V W : Type} {H : SimpleGraph V} {G : SimpleGraph W}
variable {s₁ s₂ : Finset V} {t₁ t₂ : Finset W}

/-- Amalgamate two induced-minor models. The two assignments agree on every vertex
    of the host separator. The branches of each shared source vertex meet at a host port. -/
noncomputable def join [DecidableEq V] [DecidableEq W]
    (L : SlabModel H G s₁ t₁) (R : SlabModel H G s₂ t₂)
    (src : EdgesCovered H s₁ s₂) (dst : EdgesCovered G t₁ t₂)
    (agree : ∀ i w, w ∈ t₁ → w ∈ t₂ → (w ∈ L.bag i ↔ w ∈ R.bag i))
    (link : ∀ i ∈ s₁, i ∈ s₂ → ∃ w, w ∈ L.bag i ∧ w ∈ R.bag i) :
    SlabModel H G (s₁ ∪ s₂) (t₁ ∪ t₂) := by
  let bag (i : V) := L.bag i ∪ R.bag i
  have atLeft {i w} (hs : w ∈ t₁) (hw : w ∈ bag i) : w ∈ L.bag i := by
    rcases Finset.mem_union.mp hw with h | h
    · exact h
    · exact (agree i w hs (R.within i h)).mpr h
  have atRight {i w} (hs : w ∈ t₂) (hw : w ∈ bag i) : w ∈ R.bag i := by
    rcases Finset.mem_union.mp hw with h | h
    · exact (agree i w (L.within i h) hs).mp h
    · exact h
  have within (i : V) : bag i ⊆ t₁ ∪ t₂ := Finset.union_subset_union (L.within i) (R.within i)
  refine { bag := bag, within := within, present := ?_, connected := ?_, separate := ?_, edges := ?_ }
  · intro i
    simp only [bag,Finset.union_nonempty, Finset.mem_union, L.present, R.present]
  · intro i h
    change (G.induce (↑(L.bag i ∪ R.bag i) : Set W)).Connected
    by_cases hl : i ∈ s₁
    · by_cases hr : i ∈ s₂
      · obtain ⟨w,hw,hw'⟩ := link i hl hr
        rw [Finset.coe_union]
        exact
          (G.induce_union_connected (L.connected i hl).preconnected (R.connected i hr).preconnected
            ⟨w,hw,hw'⟩)
      · have he : R.bag i = ∅ := Finset.not_nonempty_iff_eq_empty.mp (mt (R.present i).mp hr)
        rw [he,Finset.union_empty]
        exact L.connected i hl
    · have he : L.bag i = ∅ := Finset.not_nonempty_iff_eq_empty.mp (mt (L.present i).mp hl)
      rw [he,Finset.empty_union]
      exact R.connected i ((Finset.mem_union.mp h).resolve_left hl)
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro w hi hj
    rcases Finset.mem_union.mp (within i hi) with h | h
    · exact Finset.disjoint_left.mp (L.separate hij) (atLeft h hi) (atLeft h hj)
    · exact Finset.disjoint_left.mp (R.separate hij) (atRight h hi) (atRight h hj)
  · intro i j hij
    constructor
    · rintro ⟨hi,hj,he⟩
      rcases src hi hj he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · obtain ⟨x,hx,y,hy,exy⟩ := (L.edges hij).mp ⟨h₁,h₂,he⟩
        exact ⟨x,Finset.mem_union_left _ hx,y,Finset.mem_union_left _ hy,exy⟩
      · obtain ⟨x,hx,y,hy,exy⟩ := (R.edges hij).mp ⟨h₁,h₂,he⟩
        exact ⟨x,Finset.mem_union_right _ hx,y,Finset.mem_union_right _ hy,exy⟩
    · rintro ⟨x,hx,y,hy,he⟩
      rcases dst (within i hx) (within j hy) he with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · obtain ⟨hi,hj,ij⟩ := (L.edges hij).mpr ⟨x,atLeft h₁ hx,y,atLeft h₂ hy,he⟩
        exact ⟨Finset.mem_union_left _ hi,Finset.mem_union_left _ hj,ij⟩
      · obtain ⟨hi,hj,ij⟩ := (R.edges hij).mpr ⟨x,atRight h₁ hx,y,atRight h₂ hy,he⟩
        exact ⟨Finset.mem_union_right _ hi,Finset.mem_union_right _ hj,ij⟩

/-- With the whole target present, a slab model gives the usual unrestricted induced minor. -/
theorem toInducedMinor [Fintype V] {t : Finset W} (M : SlabModel H G Finset.univ t) :
    IsInducedMinor H G := by
  refine ⟨{
    bag := M.bag
    inhabited := fun i => (M.present i).mpr (Finset.mem_univ _)
    connected := fun i => M.connected i (Finset.mem_univ _)
    separate := M.separate
    edges := fun {_ _} hij => ?_ }⟩
  simpa only [Finset.mem_univ, true_and] using M.edges hij

end SlabModel
end UnitIntervalMinors
