module

public import SolvedMath.HigherInversionComponents
public import SolvedMath.HigherInversionCertificates

@[expose] public section

namespace HigherInversionLimits
open Certificate

/-- A nontrivial direct-sum cut after j places in a one-based permutation. -/
def hasCut (w : List ℕ) : Bool :=
  (List.range w.length).any fun j => 0<j && (w.take j).all (· ≤ j)

/-- Enumerate the empty decoration and all permitted nontrivial components up to inversion weight e. -/
def decorations (e : ℕ) (forbidden : List ℕ) : List (List ℕ) :=
  [] :: (List.range (e+2)).flatMap fun n =>
    if n<2 then [] else
    (((List.range n).map (·+1)).permutations').filter fun w =>
      StableInversions.invCount w ≤ e && !hasCut w && !occursB forbidden w

def coefficientTerm (e : ℕ) (p : List ℕ) (b : Boundary) (g h : List ℕ) : ℤ :=
  let w := StableInversions.invCount g + StableInversions.invCount h
  if e<w then 0 else
    let previous := if w=e then avoidanceIndicator p b.decomposable g h
      else avoidanceIndicator p (b.indecomposable (min (e-w-1) 4)) g h
    previous - avoidanceIndicator p (b.indecomposable (min (e-w) 4)) g h

/-- The signed coefficient of degree d+1 in the template formula. -/
def slopeCoefficient (p : List ℕ) (d : ℤ) : ℤ :=
  if d < -1 then 0 else
    let e := (d+1).toNat
    ((decorations e [1,3,2]).map fun g => ((decorations e [2,1,3]).map fun h =>
      ((orientations p).map fun ⟨q,b⟩ => coefficientTerm e q b g h).sum).sum).sum

private theorem indicator_agrees {p q : List ℕ} {b : Boundary} (hp : p ∈ secondary)
    (hs : (q,b) ∈ orientations p) (t : ℕ) (g h : List ℕ) :
    avoidanceIndicator q (b.indecomposable (min t 4)) g h = avoidanceIndicator q b.decomposable g h := by
  have same := arbitrary_cores_agree hp hs (min t 4) (by omega) g h
  have tests := (accepts_iff q b.decomposable g h).trans
    (same.trans (accepts_iff q (b.indecomposable (min t 4)) g h).symm)
  unfold avoidanceIndicator
  split <;> split <;> simp_all

private theorem secondary_term_zero {p q : List ℕ} {b : Boundary} (hp : p ∈ secondary)
    (hs : (q,b) ∈ orientations p) (e : ℕ) (g h : List ℕ) : coefficientTerm e q b g h = 0 := by
  simp only [coefficientTerm]
  split
  · rfl
  · rw [indicator_agrees hp hs _ g h, indicator_agrees hp hs _ g h]
    simp

private theorem sum_of_zeros {α : Type} (xs : List α) (f : α → ℤ)
    (zero : ∀ x ∈ xs, f x=0) : (xs.map f).sum=0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [zero x (by simp), ih (fun y hy => zero y (by simp [hy]))]
    rfl

/-- All coefficients vanish at every integer diagonal for each of the six secondary partners. -/
theorem secondary_coefficients_zero {p : List ℕ} (p_mem : p ∈ secondary) (d : ℤ) :
    slopeCoefficient p d = 0 := by
  unfold slopeCoefficient
  split
  · rfl
  · apply sum_of_zeros
    intro g _
    apply sum_of_zeros
    intro h _
    apply sum_of_zeros
    rintro ⟨q,b⟩ hs
    exact secondary_term_zero p_mem hs _ g h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem tertiary_coefficients :
    tertiary.map (fun p => [slopeCoefficient p (-1), slopeCoefficient p 0, slopeCoefficient p 1]) =
      [[-2,0,0],[3,6,15],[0,1,2],[0,2,4],[0,0,2]] := by decide +kernel

/-- Contracts for the coefficients derived from actual permutation counts. -/
def Secondary (p : List ℕ) : Prop := ∀ d : ℤ, EventuallyConstant (diagonalDifference [p] d)

def Tertiary (p : List ℕ) : Prop := ∀ d : ℤ,
  EventuallyConstant (fun n => diagonalDifference [p] d (n+1) - diagonalDifference [p] d n)

private theorem tertiary_nonzero {p : List ℕ} (hp : p ∈ tertiary) :
    ∃ d : ℤ, slopeCoefficient p d ≠ 0 := by
  have row := List.mem_map_of_mem
    (f := fun p => [slopeCoefficient p (-1), slopeCoefficient p 0, slopeCoefficient p 1]) hp
  rw [tertiary_coefficients] at row
  by_contra! h
  simp [h] at row

/-- The remaining structural hypothesis is the exact signed slope formula on the source permutations. -/
theorem problem84_of_template_formula
    (formula : ∀ p ∈ secondary ++ tertiary, ∀ d : ℤ,
      EventuallyAffine (diagonalDifference [p] d) (slopeCoefficient p d)) :
    (∀ p ∈ secondary, Secondary p) ∧ (∀ p ∈ tertiary, Tertiary p ∧ ¬ Secondary p) := by
  constructor
  · intro p hp d
    exact (affine_constant_iff (formula p (List.mem_append_left _ hp) d)).mpr
      (secondary_coefficients_zero hp d)
  · intro p hp
    have hp' := List.mem_append_right secondary hp
    constructor
    · intro d
      exact ⟨_, affine_difference (formula p hp' d)⟩
    · intro collapse
      obtain ⟨d, hd⟩ := tertiary_nonzero hp
      exact hd ((affine_constant_iff (formula p hp' d)).mp (collapse d))

end HigherInversionLimits
