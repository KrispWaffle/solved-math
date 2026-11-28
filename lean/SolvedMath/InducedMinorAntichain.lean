module

public import SolvedMath.InducedMinorBands

@[expose] public section

namespace InducedMinorBands

open SimpleGraph BipartiteInducedIsomorphism
open scoped Classical

namespace Model

variable {n m : ℕ} (M : Model (exampleGraph n) (exampleGraph m))

private noncomputable def rep (a : Vertex n) := (M.inhabited a).choose

private theorem rep_mem (a : Vertex n) : M.rep a ∈ M.bag a := (M.inhabited a).choose_spec

private theorem rep_inj : Function.Injective M.rep := by
  intro a b h
  by_contra hn
  exact Finset.disjoint_left.mp (M.separate hn) (M.rep_mem a) (h ▸ M.rep_mem b)

private noncomputable def center (i : Fin (n+2)) := row (M.rep (core i 0))

private theorem aligned (i : Fin (n+2)) {a b : Vertex n} (ha : row a = i.val+1)
    (hb : row b = i.val+1) (hab : a ≠ b) {x y : Vertex m} (hx : x ∈ M.bag a)
    (hy : y ∈ M.bag b) : row x = row y := by
  apply M.common_neighbors_force_row slot (positions_unique m) hab ?_
    ⟨commonVertex i,common_inj i⟩ (fun k => ⟨internal_common i a ha k,internal_common i b hb k⟩) hx hy
  change ¬ Near (row a) (row b)
  rw [ha,hb]
  rintro (h|h) <;> omega

private theorem in_center (i : Fin (n+2)) {a : Vertex n} (h : row a = i.val+1)
    {x : Vertex m} (hx : x ∈ M.bag a) : row x = M.center i := by
  by_cases he : a = core i 0
  · subst a
    have hne : core i 0 ≠ core i 1 := by simp [core]
    have h₁ := M.aligned i rfl rfl hne hx (M.rep_mem (core i 1))
    have h₂ := M.aligned i rfl rfl hne (M.rep_mem (core i 0)) (M.rep_mem (core i 1))
    exact h₁.trans h₂.symm
  · exact M.aligned i h rfl he hx (M.rep_mem (core i 0))

private theorem centers_step (i j : Fin (n+2)) (h : i.val+1 = j.val) :
    Near (M.center i) (M.center j) := by
  have adj : (exampleGraph n).Adj (core i 0) (core j 0) := Or.inl (by dsimp [core,row]; omega)
  obtain ⟨x,hx,y,hy,hadj⟩ := (M.edges adj.ne).mp adj
  change Near (row x) (row y) at hadj
  rwa [M.in_center i rfl hx,M.in_center j rfl hy] at hadj

private theorem end_full (b : Bool) : Function.Surjective
    (fun j => slot (M.rep (endVertex n b j))) := by
  apply Finite.surjective_of_injective
  intro j k h
  apply end_injective n b
  apply M.rep_inj
  apply positions_unique m
  exact Prod.ext ((M.in_center _ (end_pos n b j) (M.rep_mem _)).trans
    (M.in_center _ (end_pos n b k) (M.rep_mem _)).symm) h

private theorem triple_position (x : Vertex m) (hx : slot x = 2) : row x = 1 ∨ row x = m+2 := by
  rcases x with (⟨i,j⟩ | b)
  · have h := congrArg Fin.val hx
    dsimp [slot] at h
    omega
  · cases b <;> simp [row]

private theorem end_marked (b : Bool) : M.center (endRow n b) = 1 ∨
    M.center (endRow n b) = m+2 := by
  obtain ⟨j,hj⟩ := M.end_full b 2
  have h := triple_position _ hj
  rwa [M.in_center _ (end_pos n b j) (M.rep_mem _)] at h

private theorem ends_different : M.center (endRow n false) ≠ M.center (endRow n true) := by
  intro h
  let a := endVertex n false 0
  obtain ⟨j,hj⟩ := M.end_full true (slot (M.rep a))
  have hrow := (M.in_center _ (end_pos n true j) (M.rep_mem _)).trans
    (h.symm.trans (M.in_center _ (end_pos n false 0) (M.rep_mem _)).symm)
  have e := M.rep_inj (positions_unique m (Prod.ext hrow hj))
  have eqr := congrArg row e
  change row (endVertex n true j) = row (endVertex n false 0) at eqr
  rw [end_pos, end_pos] at eqr
  simp [endRow] at eqr

private theorem span_bound :
    M.center (endRow n false) ≤ M.center (endRow n true) + (n+1) ∧
    M.center (endRow n true) ≤ M.center (endRow n false) + (n+1) := by
  let f (k : ℕ) := M.center ⟨min k (n+1),by omega⟩
  have hop (k : ℕ) (hk : k < n+1) : Near (f k) (f (k+1)) := by
    apply M.centers_step
    change min k (n+1) + 1 = min (k+1) (n+1)
    omega
  have bounds (k : ℕ) (hk : k ≤ n+1) : f 0 ≤ f k+k ∧ f k ≤ f 0 + k := by
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨h₁,h₂⟩ := ih (by omega)
      rcases hop k (by omega) with e | e <;> omega
  simpa [f,endRow] using bounds (n+1) le_rfl

/-- Any induced-minor model between the displayed graphs preserves the whole gap. -/
theorem gap_preserved (M : Model (exampleGraph n) (exampleGraph m)) : n = m := by
  have h := Fintype.card_le_of_injective _ M.rep_inj
  simp only [Vertex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
  obtain ⟨l,r⟩ := M.span_bound
  have ne := M.ends_different
  rcases M.end_marked false with a | a <;> rcases M.end_marked true with b | b <;> omega

end Model

/-- The class of all finite bipartite permutation graphs, on arbitrary finite vertex types. -/
structure FiniteBipartitePermutation where
  Vertex : Type
  vertices : Fintype Vertex
  graph : SimpleGraph Vertex
  biperm : IsBipartitePermutation graph

def InducedMinorQuestion : Prop :=
  WellQuasiOrdered (fun H G : FiniteBipartitePermutation => IsInducedMinor H.graph G.graph)

def sequence (n : ℕ) : FiniteBipartitePermutation :=
  ⟨Vertex (n+2),inferInstance,exampleGraph (n+2),example_bipartite_permutation _⟩

theorem antichain {i j : ℕ} (h : IsInducedMinor (sequence i).graph (sequence j).graph) : i = j := by
  obtain ⟨model⟩ := h
  have he : i+2 = j+2 := Model.gap_preserved model
  omega

/-- The bipartite-permutation induced-minor question has a negative answer. -/
theorem bipartite_permutation_not_wqo : ¬ InducedMinorQuestion := by
  intro h
  obtain ⟨i,j,hlt,hm⟩ := h sequence
  exact hlt.ne (antichain hm)

end InducedMinorBands
