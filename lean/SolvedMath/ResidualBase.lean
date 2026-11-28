module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace ResidualBase

/-- Zero-based values on positions below n. The two conditions give a permutation of [0,n). -/
def Ranked (n : Nat) (v : Nat → Nat) : Prop :=
  (∀ i < n, v i < n) ∧ ∀ i < n, ∀ j < n, v i = v j → i = j

def Avoid1324 (n : Nat) (v : Nat → Nat) : Prop :=
  ∀ i j k l, i < j → j < k → k < l → l < n → v i < v k → v k < v j → v j < v l → False

def Reduced (n : Nat) (v : Nat → Nat) : Prop :=
  ∀ i, i + 1 < n → v (i + 1) ≠ v i + 1

def inversionPairs (n : Nat) (v : Nat → Nat) : Finset (Nat × Nat) :=
  ((Finset.range n) ×ˢ (Finset.range n)).filter (fun p => p.1 < p.2 ∧ v p.2 < v p.1)

def shell (n : Nat) (v : Nat → Nat) (t : Nat) : Finset (Nat × Nat) :=
  (inversionPairs n v).filter (fun p => min p.1 (n - 1 - p.2) = t)

private theorem mem_shell {n t i j : Nat} {v : Nat → Nat} :
    (i,j) ∈ shell n v t ↔ i < n ∧ j < n ∧ i < j ∧ v j < v i ∧ min i (n-1-j) = t := by
  simp [shell, inversionPairs, and_assoc]

private theorem middle_increasing {n lo hi i j : Nat} {v : Nat → Nat}
    (rank : Ranked n v) (avoid : Avoid1324 n v) (hn : hi < n)
    (li : lo ≤ i) (ij : i < j) (jh : j ≤ hi)
    (_ai : v lo ≤ v i) (aj : v lo ≤ v j) (ib : v i ≤ v hi) (_jb : v j ≤ v hi) :
    v i < v j := by
  have ln : lo < n := by omega
  have inn : i < n := by omega
  have jn : j < n := by omega
  by_contra! wrong
  have ne : v i ≠ v j := fun h => (Nat.ne_of_lt ij) (rank.2 _ inn _ jn h)
  have jl : v lo ≠ v j := fun h => (by omega : lo ≠ j) (rank.2 _ ln _ jn h)
  have ih : v i ≠ v hi := fun h => (by omega : i ≠ hi) (rank.2 _ inn _ hn h)
  have lin : lo < i := by
    by_contra! h
    have e : i = lo := by omega
    rw [e] at wrong ne
    omega
  have jhi : j < hi := by
    by_contra! h
    have e : j = hi := by omega
    rw [e] at wrong ne
    omega
  exact avoid lo i j hi lin ij jhi hn (by omega) (by omega) (by omega)

private theorem separated_scores {n i j : Nat} {v : Nat → Nat}
    (reduced : Reduced n v) (hn : j < n) (ij : i < j) (vals : v i < v j) :
    i + v i + 3 ≤ j + v j := by
  by_cases next : j = i + 1
  · have gap := reduced i (by omega)
    rw [← next] at gap
    omega
  · omega

/-- Removing the two endpoints of a cropped interval charges this many distinct
inversions. Positions and values continue to use the original alphabet. -/
theorem shell_charge {n : Nat} {v : Nat → Nat} (rank : Ranked n v)
    (avoid : Avoid1324 n v) (reduced : Reduced n v) (t : Nat) (room : 2*t+2 ≤ n) :
    n / 2 ≤ (shell n v t).card + 2*t := by
  classical
  let hi := n-1-t
  let W := Finset.Icc t hi
  have th : t < hi := by dsimp [hi]; omega
  have hn : hi < n := by dsimp [hi]; omega
  have tn : t < n := by omega
  have wcard : W.card = n - 2*t := by simp [W,hi]; omega
  let C := W.filter (fun i => v t ≤ v i ∧ v i ≤ v hi)
  have sub : C ⊆ W := Finset.filter_subset _ _
  have ww : ∀ i ∈ W, t ≤ i ∧ i ≤ hi := fun _ h => Finset.mem_Icc.mp h
  have cc : ∀ i ∈ C, (t ≤ i ∧ i ≤ hi) ∧ (v t ≤ v i ∧ v i ≤ v hi) :=
    fun _ h => ⟨ww _ (Finset.mem_filter.mp h).1,(Finset.mem_filter.mp h).2⟩
  have ne : v t ≠ v hi := fun h => th.ne (rank.2 _ tn _ hn h)
  let code := fun i : Nat => if v i < v t then (t,i) else (i,hi)
  have boundary (i : Nat) (range : t ≤ i ∧ i ≤ hi)
      (outside : v i < v t ∨ v hi < v i) : code i ∈ shell n v t := by
    dsimp [code]
    split
    next h =>
      have e : t ≠ i := by rintro rfl; omega
      apply mem_shell.mpr
      refine ⟨tn, by omega, by omega, h, ?_⟩
      apply Nat.min_eq_left
      dsimp [hi] at range
      omega
    next h =>
      have vh : v hi < v i := by omega
      have e : i ≠ hi := by rintro rfl; omega
      apply mem_shell.mpr
      refine ⟨by omega, hn, by omega, vh, ?_⟩
      have b : n-1-hi=t := by dsimp [hi]; omega
      rw [b,Nat.min_eq_right range.1]
  have unique {i j : Nat} (ni : i ≠ t) (nj : j ≠ t) (h : code i = code j) : i = j := by
    dsimp [code] at h
    split at h <;> split at h <;> simp_all
  by_cases order : v t < v hi
  · have outside : (W \ C).card ≤ (shell n v t).card := by
      have tc : t ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl,th.le⟩,le_rfl,order.le⟩
      apply Finset.card_le_card_of_injOn code
      · intro i hw
        obtain ⟨hw,hc⟩ := Finset.mem_sdiff.mp hw
        apply boundary _ (ww _ hw)
        by_contra! h
        exact hc (Finset.mem_filter.mpr ⟨hw,by omega⟩)
      · intro i hi' j hj' e
        exact unique (fun he => (Finset.mem_sdiff.mp hi').2 (he ▸ tc))
          (fun he => (Finset.mem_sdiff.mp hj').2 (he ▸ tc)) e
    have vsub : Finset.Icc (v t) (v hi) ⊆ Finset.range n := by
      intro y hy
      have := (Finset.mem_Icc.mp hy).2
      have := rank.1 hi hn
      exact Finset.mem_range.mpr (by omega)
    have letters : (W \ C).card ≤ (Finset.range n \ Finset.Icc (v t) (v hi)).card := by
      apply Finset.card_le_card_of_injOn v
      · intro i hw
        obtain ⟨hw,hc⟩ := Finset.mem_sdiff.mp hw
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (rank.1 i (by have := ww _ hw; omega)), ?_⟩
        exact fun h => hc (Finset.mem_filter.mpr ⟨hw,Finset.mem_Icc.mp h⟩)
      · intro i h j h' e
        have wi := ww _ (Finset.mem_sdiff.mp h).1
        have wj := ww _ (Finset.mem_sdiff.mp h').1
        exact rank.2 _ (by omega) _ (by omega) e
    let slot := fun i => ((i-t) + (v i-v t)) / 3
    let slots := ((hi-t)+(v hi-v t))/3+1
    have pack : C.card ≤ slots := by
      rw [← Finset.card_range slots]
      apply Finset.card_le_card_of_injOn slot
      · intro i hiC
        have := cc _ hiC
        apply Finset.mem_range.mpr
        dsimp [slot,slots]
        omega
      · intro i hic j hjc e
        have ⟨il,iv⟩ := cc _ hic
        have ⟨jl,jv⟩ := cc _ hjc
        dsimp [slot] at e
        rcases lt_trichotomy i j with lt | eq | gt
        · have vl := middle_increasing rank avoid hn il.1 lt jl.2 iv.1 jv.1 iv.2 jv.2
          have := separated_scores reduced (by omega : j < n) lt vl
          omega
        · exact eq
        · have vl := middle_increasing rank avoid hn jl.1 gt il.2 jv.1 iv.1 jv.2 iv.2
          have := separated_scores reduced (by omega : i < n) gt vl
          omega
    rw [Finset.card_sdiff_of_subset sub,wcard] at outside letters
    rw [Finset.card_sdiff_of_subset vsub, Finset.card_range,Nat.card_Icc] at letters
    dsimp only [slots] at pack
    have ends : hi + t + 1 = n := by dsimp [hi]; omega
    have ccSize := Finset.card_le_card sub
    rw [wcard] at ccSize
    have bound := rank.1 hi hn
    omega
  · have rev : v hi < v t := by omega
    have all : (W.erase t).card ≤ (shell n v t).card := by
      apply Finset.card_le_card_of_injOn code
      · intro i hw
        obtain ⟨_,hw⟩ := Finset.mem_erase.mp hw
        exact boundary _ (ww _ hw) (by omega)
      · intro i h j h' e
        exact unique (Finset.mem_erase.mp h).1 (Finset.mem_erase.mp h').1 e
    rw [Finset.card_erase_of_mem (Finset.mem_Icc.mpr ⟨by omega,th.le⟩),wcard] at all
    omega

/-- All sufficiently long reduced 1324-avoiders already have enough inversions
for the full base inequality, even before the forced doublings. -/
theorem long_skeleton {n : Nat} {v : Nat → Nat} (rank : Ranked n v)
    (avoid : Avoid1324 n v) (reduced : Reduced n v) (long : 44 ≤ n) :
    3*n ≤ (inversionPairs n v).card + 3 := by
  classical
  have dis : ((Finset.range 11 : Finset Nat) : Set Nat).PairwiseDisjoint (shell n v) := by
    intro i _ j _ h
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact h ((Finset.mem_filter.mp hp).2.symm.trans (Finset.mem_filter.mp hq).2)
  have sub : (Finset.range 11).biUnion (shell n v) ⊆ inversionPairs n v := by
    intro p hp
    obtain ⟨i, _, h⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp h).1
  have total := Finset.card_le_card sub
  rw [Finset.card_biUnion dis] at total
  have shells := Finset.sum_le_sum (s := Finset.range 11)
    (f := fun _ : Nat => n/2) (g := fun t => (shell n v t).card + 2*t)
    (fun t ht => shell_charge rank avoid reduced t (by have := Finset.mem_range.mp ht; omega))
  rw [Finset.sum_add_distrib] at shells
  have offset : (∑ t ∈ Finset.range 11, 2*t) = 110 := by decide
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, offset] at shells
  omega


/-- A permutation is sum-decomposable if a nonempty proper prefix uses the
smallest possible values. -/
def hasCut (n : Nat) (v : Nat → Nat) : Bool :=
  (List.range n).any fun k => 0 < k && (List.range k).all fun i => v i < k

def deleteRank (v : Nat → Nat) (d i : Nat) : Nat :=
  let x := v (if i < d then i else i+1)
  if v d < x then x-1 else x

def positionOf (n : Nat) (v : Nat → Nat) (a : Nat) : Nat :=
  ((List.range n).find? (fun i => v i == a)).getD n

def extrema (n : Nat) (v : Nat → Nat) : Finset Nat :=
  {0, n-1, positionOf n v 0, positionOf n v (n-1)}

/-- Meng's unique minimal inflation keeps the four extreme deletions
indecomposable by doubling each extreme that needs protection. -/
def forced (n : Nat) (v : Nat → Nat) : Finset Nat :=
  (extrema n v).filter fun i => i < n ∧ (n = 2 ∨ hasCut (n-1) (deleteRank v i) = true)

def multiplicity (n : Nat) (v : Nat → Nat) (i : Nat) : Nat :=
  if i ∈ forced n v then 2 else 1

def baseLength (n : Nat) (v : Nat → Nat) : Nat := n + (forced n v).card

/-- Blocks increase internally. An inversion of the skeleton gives the
Cartesian product of its two inflated blocks as inversions. -/
def baseInversions (n : Nat) (v : Nat → Nat) : Nat :=
  ∑ p ∈ inversionPairs n v, multiplicity n v p.1 * multiplicity n v p.2

theorem forced_card_le (n : Nat) (v : Nat → Nat) : (forced n v).card ≤ 4 := by
  have h := Finset.card_le_card (Finset.filter_subset (s := extrema n v)
    (fun i => i < n ∧ (n = 2 ∨ hasCut (n-1) (deleteRank v i) = true)))
  unfold extrema at h
  simpa only [forced, extrema] using h.trans (by
    apply (Finset.card_insert_le ..).trans
    apply Nat.succ_le_succ
    apply (Finset.card_insert_le ..).trans
    apply Nat.succ_le_succ
    apply (Finset.card_insert_le ..).trans
    simp)

theorem inversionPairs_le_base (n : Nat) (v : Nat → Nat) :
    (inversionPairs n v).card ≤ baseInversions n v := by
  have one (i : Nat) : 1 ≤ multiplicity n v i := by unfold multiplicity; split <;> decide
  have h := Finset.sum_le_sum (s := inversionPairs n v) (f := fun _ => 1)
    (g := fun p => multiplicity n v p.1 * multiplicity n v p.2)
    (fun p _ => show 1 ≤ _ from Nat.mul_pos (one _) (one _))
  simpa [baseInversions] using h

/-- The source statement on every reduced skeleton defining a base residual. -/
def MengBaseInequality : Prop :=
  ∀ n v, 2 ≤ n → Ranked n v → Avoid1324 n v → Reduced n v → hasCut n v = false →
    3 * baseLength n v ≤ baseInversions n v + 15

/-- The precise finite implication evaluated by the accompanying census. -/
def ShortCensus : Prop :=
  ∀ n v, 2 ≤ n → n ≤ 43 → Ranked n v → Avoid1324 n v → Reduced n v → hasCut n v = false →
    (inversionPairs n v).card ≤ 3*n-4 → 3 * baseLength n v ≤ baseInversions n v + 15

theorem meng_base_of_short_census (checked : ShortCensus) : MengBaseInequality := by
  intro n v hn rank avoid reduced indecomp
  have size := forced_card_le n v
  have weight := inversionPairs_le_base n v
  by_cases long : 44 ≤ n
  · have h := long_skeleton rank avoid reduced long
    unfold baseLength
    omega
  · by_cases low : (inversionPairs n v).card ≤ 3*n-4
    · exact checked n v hn (by omega) rank avoid reduced indecomp low
    · unfold baseLength
      omega

end ResidualBase
