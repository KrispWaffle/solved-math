module

public import SolvedMath.InducedMinorRows

@[expose] public section

namespace InducedMinorBands

open SimpleGraph BipartiteInducedIsomorphism

/-- Two ordinary vertices in every row, and one extra in each of the two marked rows. -/
abbrev Vertex (n : ℕ) := (Fin (n+4) × Fin 2) ⊕ Bool

def row {n : ℕ} : Vertex n → ℕ
  | .inl (i,_) => i.val
  | .inr false => 1
  | .inr true => n+2

def slot {n : ℕ} : Vertex n → Fin 3
  | .inl (_,j) => j.castSucc
  | .inr _ => 2

theorem positions_unique (n : ℕ) : Function.Injective
    (fun x : Vertex n => (row x,slot x)) := by
  rintro (⟨i,u⟩ | b) (⟨j,v⟩ | c) h
  · have hi := congrArg Prod.fst h
    have hv := congrArg (fun t : ℕ × Fin 3 => t.2.val) h
    dsimp [row,slot] at hi hv
    exact congrArg Sum.inl (Prod.ext (Fin.ext hi) (Fin.ext hv))
  · have hv := congrArg (fun t : ℕ × Fin 3 => t.2.val) h
    dsimp [slot] at hv
    omega
  · have hv := congrArg (fun t : ℕ × Fin 3 => t.2.val) h
    dsimp [slot] at hv
    omega
  · have hr := congrArg Prod.fst h
    cases b <;> cases c <;> simp_all [row]

abbrev exampleGraph (n : ℕ) := band (@row n)

/-- The two orders swap alternate adjacent pairs of rows, keeping the order of twins. -/
def rank (bottom : Bool) {n : ℕ} (x : Vertex n) : ℕ :=
  3 * (2 * row x + (if (row x % 2 == 0) == bottom then 3 else 0)) + (slot x).val

private theorem rank_inj (b : Bool) (n : ℕ) : Function.Injective (@rank b n) := by
  intro x y h
  apply positions_unique n
  apply Prod.ext
  · change row x = row y
    unfold rank at h
    split at h <;> split at h <;> omega
  · apply Fin.ext
    change (slot x).val = (slot y).val
    unfold rank at h
    split at h <;> split at h <;> omega

theorem example_bipartite_permutation (n : ℕ) : IsBipartitePermutation (exampleGraph n) := by
  constructor
  · refine ⟨fun x => decide (row x % 2 = 0), ?_⟩
    intro x y h
    change Near (row x) (row y) at h
    rcases h with h | h <;> simp only [ne_eq,decide_eq_decide] <;> omega
  · refine ⟨⟨_,rank_inj false n⟩,⟨_,rank_inj true n⟩,?_⟩
    intro x y
    change Near (row x) (row y) ↔
      (rank false x < rank false y ∧ rank true y < rank true x) ∨
      (rank false y < rank false x ∧ rank true x < rank true y)
    cases hx : (row x % 2 == 0) <;> cases hy : (row y % 2 == 0)
    all_goals simp [rank,hx,hy,Near,FoldedLinearForests.Consecutive]
    all_goals simp only [beq_iff_eq, beq_eq_false_iff_ne] at hx hy
    all_goals omega

/-- A row of the interior, indexed from the left marked row. -/
def core {n : ℕ} (i : Fin (n+2)) (j : Fin 2) : Vertex n :=
  .inl (⟨i.val+1,by omega⟩,j)

def commonVertex {n : ℕ} (i : Fin (n+2)) (z : Fin 4) : Vertex n :=
  .inl (⟨if z.val < 2 then i.val else i.val+2,by split <;> omega⟩, ⟨z.val%2,by omega⟩)

theorem common_inj {n : ℕ} (i : Fin (n+2)) : Function.Injective (commonVertex i) := by
  intro z w h
  have hr := congrArg row h
  have hs := congrArg (fun x => (slot x).val) h
  dsimp [row,slot,commonVertex] at hr hs
  apply Fin.ext
  split at hr <;> split at hr <;> omega

theorem internal_common {n : ℕ} (i : Fin (n+2)) (a : Vertex n) (h : row a = i.val+1)
    (k : Fin 4) : (exampleGraph n).Adj a (commonVertex i k) := by
  change Near (row a) (if k.val < 2 then i.val else i.val+2)
  rw [h]
  dsimp [Near,FoldedLinearForests.Consecutive]
  split <;> omega

def endRow (n : ℕ) : Bool → Fin (n+2)
  | false => 0
  | true => ⟨n+1,by omega⟩

def endVertex (n : ℕ) (b : Bool) (j : Fin 3) : Vertex n :=
  if hj : j.val < 2 then core (endRow n b) ⟨j.val,hj⟩ else .inr b

private theorem end_slot (n : ℕ) (b : Bool) (j : Fin 3) : slot (endVertex n b j) = j := by
  apply Fin.ext
  unfold endVertex
  split
  · rfl
  · change 2 = j.val
    omega

theorem end_injective (n : ℕ) (b : Bool) : Function.Injective (endVertex n b) := by
  intro i j e
  simpa only [end_slot] using congrArg slot e

theorem end_pos (n : ℕ) (b : Bool) (j : Fin 3) : row (endVertex n b j) = (endRow n b).val+1 := by
  unfold endVertex
  split
  · rfl
  · cases b <;> simp [row,endRow]

end InducedMinorBands
