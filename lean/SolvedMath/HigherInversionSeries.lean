module

public import SolvedMath.HigherInversionClassification

@[expose] public section

namespace HigherInversionLimits.Series
open Certificate

inductive Rule where
  | same
  | gain (shift : Fin 3) (bad : List Requirement)
  | loss (bad : List Requirement)
  deriving DecidableEq, Repr

/-- A clause (a,b) excludes cores containing a on the left and b on the right. -/
def eitherCore (a b : List ℕ) : List Requirement := [(a,[]),([],b)]

def rule : Boundary → List ℕ → Rule
  | .firstLast, [2,1,4,3] => .loss (eitherCore [2,1] [2,1])
  | .firstLast, [3,1,4,2] => .gain 0 []
  | .firstMaximum, [2,4,1,3] => .gain 0 []
  | .firstLast, [4,1,3,2] => .gain 1 [([],[4,1,3,2])]
  | .firstMaximum, [3,4,1,2] => .gain 1 (eitherCore [3,4,1,2] [3,4,1,2])
  | .firstLast, [4,2,3,1] => .gain 2 (eitherCore [2,3,1] [3,1,2])
  | _, _ => .same

def always : List Requirement := [([],[])]

def ruleCheck (r : Rule) (d j : List Requirement) (t : ℕ) : Bool :=
  match r with
  | .same => equivalent d j
  | .gain shift bad => equivalent d bad &&
      equivalent j (if t < shift.val then bad else always)
  | .loss bad => equivalent d always && equivalent j bad

def checkOrientation (q : List ℕ) (b : Boundary) : Bool :=
  let d := requirements q b.decomposable
  (List.range 5).all fun t =>
    ruleCheck (rule b q) d (requirements q (b.indecomposable t)) t

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem five_rule_certificate : tertiary.all (fun p =>
    (orientations p).all (fun ⟨q,b⟩ => checkOrientation q b)) = true := by decide +kernel

def weight (bad : List Requirement) (g h : List ℕ) : ℤ :=
  if bad.any (fun r => occursB r.1 g && occursB r.2 h) then 0 else 1

theorem weight_eq_zero_iff (bad : List Requirement) (g h : List ℕ) :
    weight bad g h = 0 ↔ satisfies bad g h := by
  simp [weight, satisfies, List.any_eq_true, occursB_iff]

private theorem equivalent_weight {a b : List Requirement} (eqv : equivalent a b = true)
    (g h : List ℕ) : weight a g h = weight b g h := by
  have pred := equivalent_sound eqv g h
  have congr := (weight_eq_zero_iff a g h).trans (pred.trans (weight_eq_zero_iff b g h).symm)
  unfold weight at *
  split <;> split <;> simp_all

@[simp] theorem always_weight (g h : List ℕ) : weight always g h = 0 := by
  apply (weight_eq_zero_iff _ _ _).mpr
  exact ⟨([],[]), by simp [always], ⟨[], List.nil_sublist _, rfl⟩, ⟨[], List.nil_sublist _, rfl⟩⟩

@[simp] theorem unrestricted_weight (g h : List ℕ) : weight [] g h = 1 := by rfl

def Rule.atBase (r : Rule) (actual : ℤ) (g h : List ℕ) : ℤ :=
  match r with
  | .same => actual
  | .gain _ bad => weight bad g h
  | .loss _ => 0

def Rule.atOverlap (r : Rule) (actual : ℤ) (t : ℕ) (g h : List ℕ) : ℤ :=
  match r with
  | .same => actual
  | .gain shift bad => if t < shift.val then weight bad g h else 0
  | .loss bad => weight bad g h

theorem ruleCheck_sound {r : Rule} {d j : List Requirement} {t : ℕ}
    (check : ruleCheck r d j t = true) (g h : List ℕ) :
    weight d g h = r.atBase (weight d g h) g h ∧
    weight j g h = r.atOverlap (weight d g h) t g h := by
  cases r with
  | same => exact ⟨rfl, (equivalent_weight check g h).symm⟩
  | gain shift bad =>
    obtain ⟨base, later⟩ := Bool.and_eq_true_iff.mp check
    refine ⟨equivalent_weight base g h, ?_⟩
    have proof := equivalent_weight later g h
    by_cases t < shift.val <;> simp_all [Rule.atOverlap]
  | loss bad =>
    obtain ⟨base, later⟩ := Bool.and_eq_true_iff.mp check
    exact ⟨(equivalent_weight base g h).trans (always_weight _ _), equivalent_weight later g h⟩

theorem overlap_indicators {p q : List ℕ} {b : Boundary} (hp : p ∈ tertiary)
    (orientation : (q,b) ∈ orientations p) (t : ℕ) (g h : List ℕ) :
    avoidanceIndicator q b.decomposable g h =
      (rule b q).atBase (avoidanceIndicator q b.decomposable g h) g h ∧
    avoidanceIndicator q (b.indecomposable (min t 4)) g h =
      (rule b q).atOverlap (avoidanceIndicator q b.decomposable g h) (min t 4) g h := by
  have h1 := List.all_eq_true.mp five_rule_certificate p hp
  have h2 := List.all_eq_true.mp h1 (q,b) orientation
  have h3 := List.all_eq_true.mp h2 (min t 4) (List.mem_range.mpr (by omega))
  exact ruleCheck_sound h3 g h

/-- A gain contributes its indicator at one weight shift. A loss subtracts it at the unshifted weight. -/
def Rule.coeff (r : Rule) (e w : ℕ) (g h : List ℕ) : ℤ :=
  match r with
  | .same => 0
  | .gain shift bad => if e=w+shift.val then weight bad g h else 0
  | .loss bad => if e=w then -weight bad g h else 0

private theorem one_step (r : Rule) (e w : ℕ) (base : ℤ) (g h : List ℕ) :
    (if e<w then 0 else
      (if w=e then r.atBase base g h else r.atOverlap base (min (e-w-1) 4) g h) -
        r.atOverlap base (min (e-w) 4) g h) = r.coeff e w g h := by
  cases r with
  | same => simp [Rule.atBase, Rule.atOverlap, Rule.coeff]
  | loss bad =>
    by_cases e<w <;> by_cases w=e <;> simp_all [Rule.atBase, Rule.atOverlap, Rule.coeff] <;> omega
  | gain shift bad =>
    have hs := shift.isLt
    simp only [Rule.atBase, Rule.atOverlap, Rule.coeff]
    split_ifs <;> omega

theorem coefficientTerm_eq_rule {p q : List ℕ} {b : Boundary} (hp : p ∈ tertiary)
    (orientation : (q,b) ∈ orientations p) (e : ℕ) (g h : List ℕ) :
    coefficientTerm e q b g h =
      (rule b q).coeff e (StableInversions.invCount g + StableInversions.invCount h) g h := by
  let w := StableInversions.invCount g + StableInversions.invCount h
  let base := avoidanceIndicator q b.decomposable g h
  have later := overlap_indicators hp orientation (e-w) g h
  have prev := overlap_indicators hp orientation (e-w-1) g h
  change (if e<w then 0 else (if w=e then base else
    avoidanceIndicator q (b.indecomposable (min (e-w-1) 4)) g h) -
    avoidanceIndicator q (b.indecomposable (min (e-w) 4)) g h) = _
  calc
    _ = (if e<w then 0 else (if w=e then (rule b q).atBase base g h else
      (rule b q).atOverlap base (min (e-w-1) 4) g h) -
      (rule b q).atOverlap base (min (e-w) 4) g h) := by
        by_cases small : e<w
        · simp only [ite_eq_left small]
        · simp only [ite_eq_right small]
          apply congrArg₂ (· - ·)
          · by_cases eq : w=e
            · simp only [ite_eq_left eq]
              exact later.1
            · simp only [ite_eq_right eq]
              exact prev.2
          · exact later.2
    _ = _ := one_step _ _ _ _ _ _


def primaryRule : List ℕ → Rule
  | [2,1,4,3] => .loss (eitherCore [2,1] [2,1])
  | [2,4,1,3] => .gain 0 []
  | [2,4,3,1] => .gain 1 [([],[4,1,3,2])]
  | [3,4,1,2] => .gain 1 (eitherCore [3,4,1,2] [3,4,1,2])
  | [4,2,3,1] => .gain 2 (eitherCore [2,3,1] [3,1,2])
  | _ => .same

def multiplicity : List ℕ → ℕ
  | [2,4,1,3] => 3
  | [2,4,3,1] => 1
  | _ => 2

def orbit (p : List ℕ) : List Rule :=
  ((orientations p).map fun ⟨q,b⟩ => rule b q).filter (· != .same)

theorem orbit_certificate : tertiary.all (fun p =>
    orbit p == List.replicate (multiplicity p) (primaryRule p)) = true := by decide +kernel

private theorem omit_same (rs : List Rule) (f : Rule → ℤ) (zero : f .same = 0) :
    (rs.map f).sum = ((rs.filter (· != .same)).map f).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    by_cases hr : r=.same
    · subst r
      simp [zero, ih]
    · simp [hr, ih]

private theorem scale_sum {α : Type} (xs : List α) (m : ℤ) (f : α → ℤ) :
    (xs.map fun x => m*f x).sum = m*(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, Int.mul_add]

theorem orbit_sum {p : List ℕ} (hp : p ∈ tertiary) (e : ℕ) (g h : List ℕ) :
    ((orientations p).map (fun ⟨q,b⟩ => coefficientTerm e q b g h)).sum =
      (multiplicity p : ℤ) *
        (primaryRule p).coeff e (StableInversions.invCount g + StableInversions.invCount h) g h := by
  let f := fun (r : Rule) => r.coeff e (StableInversions.invCount g + StableInversions.invCount h) g h
  let rs := (orientations p).map (fun ⟨q,b⟩ => rule b q)
  have reduced : (orbit p) = List.replicate (multiplicity p) (primaryRule p) :=
    beq_iff_eq.mp (List.all_eq_true.mp orbit_certificate p hp)
  calc
    _ = (rs.map f).sum := by
      apply congrArg List.sum
      simp only [rs, List.map_map]
      apply List.map_congr_left
      rintro ⟨q,b⟩ orient
      exact coefficientTerm_eq_rule hp orient e g h
    _ = ((orbit p).map f).sum := omit_same rs f rfl
    _ = _ := by rw [reduced]; simp [f, List.sum_replicate]

/-- The full signed coefficient is a single shifted convolution of the two end-core families. -/
theorem five_tertiary_convolutions {p : List ℕ} (hp : p ∈ tertiary) (d : ℤ) :
    slopeCoefficient p d = if d < -1 then 0 else
      let e := (d+1).toNat
      (multiplicity p : ℤ) * ((decorations e [1,3,2]).map fun g =>
        ((decorations e [2,1,3]).map fun h =>
          (primaryRule p).coeff e (StableInversions.invCount g + StableInversions.invCount h) g h).sum).sum := by
  unfold slopeCoefficient
  split
  · rfl
  · simp only [orbit_sum hp, scale_sum]

end HigherInversionLimits.Series
