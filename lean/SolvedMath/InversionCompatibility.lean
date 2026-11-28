module

public import SolvedMath.HigherInversionLimits
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Fin.Basic

@[expose] public section

/-! Rank preservation in the substitution governing the Linusson–Verkama compatibility test. -/

namespace InversionCompatibility

/-- Zero-based rank among the retained entries of the last component. -/
def rank (s : List Nat) (x : Nat) : Nat := s.countP (· < x)

/-- The number of retained entries below the first pivot before, and after, the middle is grown. -/
def oldCut (s : List Nat) (c : Nat) : Nat := s.countP (· ≤ c)
def newCut (s : List Nat) (c : Nat) : Nat := s.countP (· < c)

private theorem rank_mono (s : List Nat) {x y : Nat} (hxy : x ≤ y) :
    rank s x ≤ rank s y := by
  induction s with
  | nil => simp [rank]
  | cons a s ih =>
    simp only [rank, List.countP_cons] at *
    split <;> split <;> simp_all <;> omega

private theorem rank_strict (s : List Nat) {x y : Nat} (hx : x ∈ s) (hxy : x<y) :
    rank s x < rank s y := by
  induction s with
  | nil => simp at hx
  | cons a s ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst a
      have le := rank_mono s (Nat.le_of_lt hxy)
      simp [rank, hxy] at *
      omega
    · have t := ih h
      simp only [rank, List.countP_cons] at *
      split <;> split <;> simp_all <;> omega

theorem rank_order {s : List Nat} {x y : Nat} (hx : x∈s) :
    rank s x < rank s y ↔ x<y := by
  constructor
  · intro h
    by_contra hn
    have hle : y ≤ x := by omega
    have := rank_mono s hle
    omega
  · exact rank_strict s hx

/-- Crossing the retained critical point loses exactly one lower value, at any restriction. -/
theorem oldCut_eq_newCut_add_one (s : List Nat) (c : Nat) (nd : s.Nodup) (hc : c∈s) :
    oldCut s c = newCut s c + 1 := by
  induction s with
  | nil => simp at hc
  | cons a s ih =>
    have nt := List.nodup_cons.mp nd
    by_cases he : a=c
    · subst a
      have equal : s.countP (· ≤ c) = s.countP (· < c) := by
        apply List.countP_congr
        intro x hx
        have hxc : x≠c := fun e => nt.1 (e ▸ hx)
        simp
        omega
      simp [oldCut, newCut, equal]
    · have hit : c∈s := (List.mem_cons.mp hc).resolve_left (Ne.symm he)
      have same := ih nt.2 hit
      simp only [oldCut, newCut, List.countP_cons] at *
      split <;> split <;> simp_all <;> omega

theorem retained_sides (s : List Nat) (c x : Nat) (nd : s.Nodup) (hc : c∈s) (hx : x∈s) :
    (rank s x < oldCut s c ↔ x≤c) ∧ (rank s x < newCut s c ↔ x<c) := by
  rw [oldCut_eq_newCut_add_one s c nd hc]
  change (rank s x < rank s c + 1 ↔ x≤c) ∧ (rank s x < rank s c ↔ x<c)
  refine ⟨?_, rank_order hx⟩
  have h := rank_order (y:=x) hc
  omega

/-- Retaining the pivot and its crossing point commutes with both source rank comparisons. -/
theorem pivot_synchronization {s T : List Nat} (retain : s.Sublist T) (nd : T.Nodup)
    {c x : Nat} (hc : c∈s) (hx : x∈s) :
    (rank T x < oldCut T c ↔ rank s x < oldCut s c) ∧
    (rank T x < newCut T c ↔ rank s x < newCut s c) ∧
    oldCut s c = newCut s c + 1 := by
  have n := nd.sublist retain
  have a := retained_sides s c x n hc hx
  have b := retained_sides T c x nd (retain.subset hc) (retain.subset hx)
  exact ⟨b.1.trans a.1.symm, b.2.trans a.2.symm, oldCut_eq_newCut_add_one s c n hc⟩

/-- A literal direct cut in a word of distinct natural labels. -/
def HasCut (w : List Nat) : Prop :=
  ∃ L R : List Nat, L≠[] ∧ R≠[] ∧ w=L++R ∧ ∀ a∈L, ∀ b∈R, a<b

private theorem head_mem_of_cut {a : Nat} {u v t : List Nat}
    (nonempty : u≠[]) (eq : a::t=u++v) : a∈u := by
  cases u with
  | nil => contradiction
  | cons b u =>
    have h : a=b := (List.cons.inj eq).1
    simp [h]

/-- A spanning inversion rules out every direct cut. -/
theorem outer_inversion {x y : Nat} (middle : List Nat) (yx : y<x) :
    ¬ HasCut (x::middle++[y]) := by
  rintro ⟨L,R,hnL,hnR,eq,cut⟩
  have hx : x∈L := head_mem_of_cut hnL eq
  have rev := congrArg List.reverse eq
  simp only [List.reverse_append, List.reverse_cons] at rev
  have right : R.reverse ≠ [] := by simpa using hnR
  have hy : y∈R.reverse := head_mem_of_cut right (by simpa [List.append_assoc] using rev)
  have bad := cut x hx y (by simpa using hy)
  omega

/-- The absence of three positions spelling the classical pattern 213. -/
def Avoids213 {n : Nat} (w : Fin n → Nat) : Prop :=
  ∀ i j k, i < j → j < k → w j < w i → w i < w k → False

/-- In the final 213-avoiding block, a genuine high replaces the crossed value at the
head of every selected lower suffix. This produces an actual ordered embedding. -/
theorem replace_maximum_of_suffix {n t : Nat} {w : Fin n → Nat} (avoids : Avoids213 w)
    {c z : Fin n} (high : w c < w z) (suffix : Fin t → Fin n)
    (inOrder : StrictMono suffix) (follows : ∀ j, c < suffix j)
    (low : ∀ j, w (suffix j) < w c) :
    StrictMono (Fin.cons (α := fun _ => Fin n) z suffix) ∧
      ∀ i j : Fin (t+1), w (Fin.cons (α := fun _ => Fin n) z suffix i) < w (Fin.cons (α := fun _ => Fin n) z suffix j) ↔
        w (Fin.cons (α := fun _ => Fin n) c suffix i) < w (Fin.cons (α := fun _ => Fin n) c suffix j) := by
  have before (j : Fin t) : z < suffix j := by
    rcases lt_trichotomy z (suffix j) with h | h | h
    · exact h
    · have := low j
      rw [← h] at this
      omega
    · exact False.elim (avoids c (suffix j) z (follows j) h (low j) high)
  constructor
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact False.elim (lt_irrefl _ hij)
      | succ j => simpa using before j
    | succ i =>
      cases j using Fin.cases with
      | zero => exact False.elim (Fin.not_lt_zero _ hij)
      | succ j => simpa using inOrder (Fin.succ_lt_succ_iff.mp hij)
  · intro i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => simp
      | succ j =>
        have := low j
        simp only [Fin.cons_zero, Fin.cons_succ]
        omega
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        have := low i
        simp only [Fin.cons_zero, Fin.cons_succ]
        omega
      | succ j => simp

/-- If the two overlapping windows obtained by dropping an endpoint have the same
relative order, the entire injectively labelled word is increasing or decreasing. -/
theorem equal_windows_monotone {n : Nat} (w : Fin (n+2) → Nat) (distinct : Function.Injective w)
    (order : ∀ i j : Fin (n+1), w i.castSucc < w j.castSucc ↔ w i.succ < w j.succ) :
    StrictMono w ∨ StrictAnti w := by
  let up (i : Fin (n+1)) : Prop := w i.castSucc < w i.succ
  have same (i : Fin (n+1)) : up i ↔ up 0 := by
    induction i using Fin.induction with
    | zero => rfl
    | succ j ih =>
      have step : up j.castSucc ↔ up j.succ := order j.castSucc j.succ
      exact step.symm.trans ih
  by_cases h : up 0
  · exact Or.inl (Fin.strictMono_iff_lt_succ.mpr (fun i => (same i).2 h))
  · apply Or.inr
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro i
    have down : ¬ w i.castSucc < w i.succ := fun a => h ((same i).1 a)
    have ne : w i.castSucc ≠ w i.succ := fun a =>
      (ne_of_lt (show i.castSucc < i.succ from Fin.castSucc_lt_succ)) (distinct a)
    omega

/-- First proper direct cut, using one-based permutation values. -/
def firstCut (w : List Nat) : Option Nat :=
  (List.range w.length).find? fun j => j > 0 && (w.take j).all (· ≤ j)

def insertPoint (w : List Nat) (pos value : Nat) : List Nat :=
  let shifted := w.map fun x => if value ≤ x then x+1 else x
  shifted.take pos ++ [value] ++ shifted.drop pos

def inverseWord (w : List Nat) : List Nat :=
  (List.range w.length).map fun i => w.idxOf (i+1) + 1

def orient (direction : Nat) (w : List Nat) : List Nat :=
  let v := if direction ≥ 2 then w.reverse.map (fun x => w.length+1-x) else w
  if direction % 2 == 1 then inverseWord v else v

def boundaryImage (w : List Nat) (d : Nat) : Option (List Nat) := do
  let v := orient d w
  let x ← v.head?
  let tail := HigherInversionLimits.standardize v.tail
  let cut ← firstCut tail
  return orient d (insertPoint (insertPoint tail cut (cut+1)) 0 x)

/-- The prescribed source injection on one-based permutations. Its domain is restricted
to 1324-avoiders in the definition of compatibility. The four failures return none. -/
def sourceImage (w : List Nat) : Option (List Nat) :=
  match firstCut w with
  | some j => some (insertPoint w j (j+1))
  | none => (List.range 4).findSome? (boundaryImage w)

/-- Definition 7.4 with every input length, every forbidden member, and the source priority. -/
def SourceCompatible (B : List (List Nat)) : Prop :=
  ∀ w : List Nat, w.Perm ((List.range w.length).map (·+1)) →
    ¬ HigherInversionLimits.occurs [1,3,2,4] w →
    (∀ p ∈ B, ¬ HigherInversionLimits.occurs p w) →
    ∀ v, sourceImage w = some v → ∀ p ∈ B, ¬ HigherInversionLimits.occurs p v

/-- An independently checkable physical input/output certificate for any finite basis. -/
theorem incompatible_of_certificate {B : List (List Nat)} {p w v : List Nat}
    (permutation : w.Perm ((List.range w.length).map (·+1)))
    (avoids : HigherInversionLimits.occursB [1,3,2,4] w = false)
    (clean : ∀ b ∈ B, HigherInversionLimits.occursB b w = false)
    (image : sourceImage w = some v) (member : p ∈ B)
    (found : HigherInversionLimits.occursB p v = true) : ¬ SourceCompatible B := by
  intro compatible
  have avoid (b t : List Nat) (h : HigherInversionLimits.occursB b t = false) :
      ¬ HigherInversionLimits.occurs b t := by
    intro here
    have yes := (HigherInversionLimits.occursB_iff b t).2 here
    simp [h] at yes
  exact compatible w permutation (avoid _ _ avoids) (fun b hb => avoid _ _ (clean b hb))
    v image p member ((HigherInversionLimits.occursB_iff p v).1 found)

/-- The concrete length-eight lower-bound example, evaluated on the actual source map. -/
theorem sharp_example_incompatible : ¬ SourceCompatible [[3,6,4,2,5,1]] := by
  apply incompatible_of_certificate (p := [3,6,4,2,5,1]) (w := [5,8,3,4,2,6,1,7])
    (v := [5,3,9,4,2,6,1,7,8])
  · decide
  · decide
  · intro b hb
    simp only [List.mem_singleton] at hb
    subst b
    decide
  · decide
  · decide
  · decide

end InversionCompatibility
