module

public import SolvedMath.HigherInversionLimits

@[expose] public section

namespace HigherInversionLimits.Certificate

inductive Portion where
  | gamma | delta | increasing (capacity : ℕ)
  deriving DecidableEq, Repr

/-- Blocks are in position order; the first coordinate orders their disjoint value intervals. -/
abbrev Block := ℕ × Portion
abbrev Requirement := List ℕ × List ℕ

def firstLastD : List Block :=
  [(2,.increasing 1),(0,.gamma),(1,.increasing 4),(4,.increasing 4),(5,.delta),(3,.increasing 1)]

def firstMaximumD : List Block :=
  [(2,.increasing 1),(0,.gamma),(1,.increasing 4),(5,.increasing 1),(3,.increasing 4),(4,.delta)]

def firstLastJ (t : ℕ) : List Block :=
  [(4,.increasing 1),(0,.gamma),(1,.increasing 4),(3,.increasing t),
   (5,.increasing 4),(6,.delta),(2,.increasing 1)]

def firstMaximumJ (t : ℕ) : List Block :=
  [(3,.increasing 1),(0,.gamma),(1,.increasing 4),(6,.increasing 1),
   (2,.increasing (t+1)),(4,.increasing 4),(5,.delta)]

def Portion.permits (whereFrom : Portion) (chunk : List ℕ) : Bool :=
  match whereFrom with
  | .increasing capacity => chunk.length ≤ capacity && decide (chunk.Pairwise (· < ·))
  | _ => true

/-- A requirement says which two patterns the arbitrary end cores must contain. -/
def collect (p : List ℕ) (seen : List (ℕ × ℕ)) (g h : List ℕ) :
    List Block → List Requirement
  | [] => if p.isEmpty then [(standardize g, standardize h)] else []
  | (level, whereFrom)::blocks =>
    (List.range (p.length+1)).flatMap fun k =>
      let chunk := p.take k
      let ordered := chunk.all fun x => seen.all fun ⟨j,y⟩ =>
        if j<level then decide (y<x) else decide (x<y)
      if whereFrom.permits chunk && ordered then
        let observed := (chunk.map fun x => (level,x)) ++ seen
        collect (p.drop k) observed
          (if whereFrom = .gamma then chunk else g)
          (if whereFrom = .delta then chunk else h) blocks
      else []

def requirements (p : List ℕ) (blocks : List Block) : List Requirement :=
  ((collect p [] [] [] blocks).eraseDups).filter fun ⟨g,h⟩ =>
    !(occursB [1,3,2] g || occursB [2,1,3] h)

def includesRequirement (r s : Requirement) : Bool := occursB r.1 s.1 && occursB r.2 s.2

def covers (a b : List Requirement) : Bool :=
  a.all fun s => b.any fun r => includesRequirement r s

def satisfies (a : List Requirement) (gamma delta : List ℕ) : Prop :=
  ∃ r ∈ a, occurs r.1 gamma ∧ occurs r.2 delta

theorem covers_sound {a b : List Requirement} (h : covers a b = true)
    (gamma delta : List ℕ) : satisfies a gamma delta → satisfies b gamma delta := by
  rintro ⟨s, hs, hg, hd⟩
  obtain ⟨r, hr, inside⟩ := List.any_eq_true.mp (List.all_eq_true.mp h s hs)
  have inds := Bool.and_eq_true_iff.mp inside
  exact ⟨r, hr, occurs_trans ((occursB_iff _ _).mp inds.1) hg,
    occurs_trans ((occursB_iff _ _).mp inds.2) hd⟩

def equivalent (a b : List Requirement) : Bool := covers a b && covers b a

theorem equivalent_sound {a b : List Requirement} (h : equivalent a b = true)
    (gamma delta : List ℕ) : satisfies a gamma delta ↔ satisfies b gamma delta :=
  ⟨covers_sound (Bool.and_eq_true_iff.mp h).1 _ _, covers_sound (Bool.and_eq_true_iff.mp h).2 _ _⟩

def inverse (p : List ℕ) := (List.range p.length).map fun i => p.idxOf (i+1) + 1
def reverseComplement (p : List ℕ) := p.reverse.map fun i => p.length + 1 - i

def secondary : List (List ℕ) :=
  [[1,2,4,3],[1,3,4,2],[1,4,3,2],[2,3,4,1],[3,4,2,1],[4,3,2,1]]

def checkPair (p : List ℕ) (d : List Block) (j : ℕ → List Block) : Bool :=
  let base := requirements p d
  (List.range 5).all fun t => equivalent base (requirements p (j t))

inductive Boundary where
  | firstLast | firstMaximum
  deriving DecidableEq, Repr

def orientations (p : List ℕ) : List (List ℕ × Boundary) :=
  [(p,.firstLast),(inverse p,.firstLast),(p,.firstMaximum),(reverseComplement p,.firstMaximum)]

def Boundary.decomposable : Boundary → List Block
  | .firstLast => firstLastD
  | .firstMaximum => firstMaximumD

def Boundary.indecomposable : Boundary → ℕ → List Block
  | .firstLast => firstLastJ
  | .firstMaximum => firstMaximumJ

def checkPartner (p : List ℕ) : Bool :=
  (orientations p).all fun ⟨pattern,b⟩ => checkPair pattern b.decomposable b.indecomposable

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem six_partner_certificate : secondary.all checkPartner = true := by decide +kernel

theorem arbitrary_cores_agree {p pattern : List ℕ} {b : Boundary}
    (partner : p ∈ secondary) (orientation : (pattern,b) ∈ orientations p)
    (t : ℕ) (ht : t<5) (gamma delta : List ℕ) :
    satisfies (requirements pattern b.decomposable) gamma delta ↔
      satisfies (requirements pattern (b.indecomposable t)) gamma delta := by
  have h := List.all_eq_true.mp six_partner_certificate p partner
  have hd := List.all_eq_true.mp h (pattern,b) orientation
  exact equivalent_sound (List.all_eq_true.mp hd t (List.mem_range.mpr ht)) _ _

def accepts (p : List ℕ) (blocks : List Block) (g h : List ℕ) : Bool :=
  (requirements p blocks).any fun r => occursB r.1 g && occursB r.2 h

theorem accepts_iff (p : List ℕ) (blocks : List Block) (g h : List ℕ) :
    accepts p blocks g h = true ↔ satisfies (requirements p blocks) g h := by
  simp only [accepts, satisfies, List.any_eq_true, Bool.and_eq_true, occursB_iff]

/-- Empty and nontrivial indecomposable decorations of inversion weight at most two. -/
def lowCores : List (List ℕ) := [[],[2,1],[2,3,1],[3,1,2]]

def avoidanceIndicator (p : List ℕ) (blocks : List Block) (g h : List ℕ) : ℤ :=
  if accepts p blocks g h then 0 else 1

def slopeTerm (e : ℕ) (p : List ℕ) (b : Boundary) (g h : List ℕ) : ℤ :=
  let w := StableInversions.invCount g + StableInversions.invCount h
  if e<w then 0 else
    let previous := if w=e then avoidanceIndicator p b.decomposable g h
      else avoidanceIndicator p (b.indecomposable (e-w-1)) g h
    previous - avoidanceIndicator p (b.indecomposable (e-w)) g h

def lowSlope (p : List ℕ) (e : ℕ) : ℤ :=
  (lowCores.map fun g => (lowCores.map fun h =>
    ((orientations p).map fun ⟨pattern,b⟩ => slopeTerm e pattern b g h).sum).sum).sum

def tertiary : List (List ℕ) :=
  [[2,1,4,3],[2,4,1,3],[2,4,3,1],[3,4,1,2],[4,2,3,1]]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem five_slope_rows :
    tertiary.map (fun p => [lowSlope p 0, lowSlope p 1, lowSlope p 2]) =
      [[-2,0,0],[3,6,15],[0,1,2],[0,2,4],[0,0,2]] := by decide +kernel

end HigherInversionLimits.Certificate
