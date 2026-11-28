module

public import SolvedMath.UnitIntervalGlue
public import SolvedMath.UnitIntervalWords

@[expose] public section

namespace UnitIntervalMinors

open SimpleGraph Set
open InducedMinorBands (Model IsInducedMinor)

structure Drawing where
  size : ℕ
  start : Fin size → ℝ

abbrev Drawing.graph (D : Drawing) := unitGraph D.start

/-- Every sequence of finite graphs given by arbitrary real closed unit intervals
    has an earlier graph that is an unrestricted induced minor of a later one. -/
def LozinMayhillQuestion : Prop :=
  WellQuasiOrdered (fun A B : Drawing => IsInducedMinor A.graph B.graph)

private noncomputable def changeHost {V W X : Type} {H : SimpleGraph V} {G : SimpleGraph W}
    {G' : SimpleGraph X} (M : Model H G) (e : G ≃g G') : Model H G' := by
  classical
  let bag (v : V) := (M.bag v).map e.toEquiv.toEmbedding
  have mem (i : V) (x : X) : x ∈ bag i ↔ e.symm x ∈ M.bag i := by
    constructor
    · rintro hx
      obtain ⟨w,hm,rfl⟩ := Finset.mem_map.mp hx
      simpa using hm
    · intro hx
      exact Finset.mem_map.mpr ⟨e.symm x,hx,e.apply_symm_apply x⟩
  refine {
    bag := bag
    inhabited := fun i => (M.inhabited i).map
    connected := ?_
    separate := ?_
    edges := ?_ }
  · intro i
    have bij : Set.BijOn e (M.bag i : Set W) (bag i : Set X) := by
      rw [show (bag i : Set X) = e '' (M.bag i : Set W) by simp [bag]]
      exact e.injective.bijOn_image
    exact (e.induce bij).connected_iff.mp (M.connected i)
  · intro i j hij
    apply Finset.disjoint_left.mpr
    exact fun x hx hy => Finset.disjoint_left.mp (M.separate hij) ((mem i x).mp hx) ((mem j x).mp hy)
  · intro i j hij
    rw [M.edges hij]
    constructor
    · rintro ⟨x,hx,y,hy,he⟩
      exact ⟨e x,Finset.mem_map_of_mem _ hx,e y,Finset.mem_map_of_mem _ hy,e.map_adj_iff.mpr he⟩
    · rintro ⟨x,hx,y,hy,he⟩
      exact ⟨e.symm x,(mem _ _).mp hx,e.symm y,(mem _ _).mp hy,e.symm.map_adj_iff.mpr he⟩

noncomputable def Drawing.sorted (D : Drawing) := D.start ∘ Tuple.sort D.start

/-- In this drawing every segment of length at least 6h has a point covered fewer than h times. -/
def SparseAt (h : ℕ) (D : Drawing) : Prop :=
  ∀ a b : ℝ, a+6*h ≤ b → ∃ x ∈ Icc a b,
    (Finset.univ.filter fun i => x ∈ Icc (D.sorted i) (D.sorted i+1)).card < h

/-- Failure to contain one prescribed unit interval graph forces low-coverage cuts. -/
theorem sparse_of_omits (A B : Drawing) (omits : ¬ IsInducedMinor A.graph B.graph) :
    SparseAt A.size B := by
  classical
  intro a b len
  by_contra! hdense
  obtain ⟨M⟩ := long_dense_segment B.sorted (Tuple.monotone_sort B.start) A.start
    (fun i => A.start i + 1) (fun _ => by linarith) a b len hdense
  let e : unitGraph B.sorted ≃g B.graph :=
    { toEquiv := Tuple.sort B.start
      map_rel_iff' := by
        intro i j
        change (_ ≠ _ ∧ _) ↔ (_ ≠ _ ∧ _)
        rw [(Tuple.sort B.start).injective.ne_iff]
        rfl }
  exact omits ⟨changeHost M e⟩

/-- The full source statement follows from well-quasi-ordering the drawings with low
    coverage cuts at each fixed threshold. The separator induction discharges this premise. -/
theorem question_of_sparse_classes
    (hs : ∀ h : ℕ, WellQuasiOrdered (fun A B : {D : Drawing // SparseAt h D} =>
      IsInducedMinor A.val.graph B.val.graph)) : LozinMayhillQuestion := by
  intro seq
  by_contra! hbad
  let tail (n : ℕ) : {D : Drawing // SparseAt (seq 0).size D} :=
    ⟨seq (n+1),sparse_of_omits _ _ (hbad 0 (n+1) (by omega))⟩
  obtain ⟨i,j,ij,model⟩ := hs (seq 0).size tail
  exact hbad (i+1) (j+1) (by omega) model

end UnitIntervalMinors
