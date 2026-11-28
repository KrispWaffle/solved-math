module

public import SolvedMath.StableInversions
public import Mathlib.Data.List.Sublists
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

namespace HigherInversionLimits

/-- The one-based relative ranks of a word of distinct natural numbers. -/
def standardize (w : List ℕ) : List ℕ :=
  w.map fun x => 1 + w.countP (· < x)

def occurs (p w : List ℕ) : Prop := ∃ z, z.Sublist w ∧ standardize z = p

def occursB (p w : List ℕ) : Bool :=
  (w.sublistsLen p.length).any fun z => standardize z == p

theorem occursB_iff (p w : List ℕ) : occursB p w = true ↔ occurs p w := by
  simp only [occursB, List.any_eq_true, beq_iff_eq, List.mem_sublistsLen]
  constructor
  · rintro ⟨z, ⟨sub, _⟩, shape⟩
    exact ⟨z, sub, shape⟩
  · rintro ⟨z, sub, shape⟩
    exact ⟨z, ⟨sub, by simpa [standardize] using congrArg List.length shape⟩, shape⟩

private theorem below_mono (w : List ℕ) {x y : ℕ} (hxy : x ≤ y) :
    w.countP (· < x) ≤ w.countP (· < y) := by
  induction w with
  | nil => simp
  | cons b w ih =>
    simp only [List.countP_cons]
    split <;> split <;> simp_all <;> omega

private theorem below_strict {x y : ℕ} (hxy : x < y) (w : List ℕ) (hx : x ∈ w) :
    w.countP (· < x) < w.countP (· < y) := by
  induction w with
  | nil => simp at hx
  | cons b w ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst b
      have hle := below_mono w (Nat.le_of_lt hxy)
      simp [hxy]
      omega
    · have hp := ih h
      simp only [List.countP_cons]
      split <;> split <;> simp_all <;> omega

private theorem standardize_map_of_order (w : List ℕ) (f : ℕ → ℕ)
    (order : ∀ a ∈ w, ∀ b ∈ w, f a < f b ↔ a < b) :
    standardize (w.map f) = standardize w := by
  simp only [standardize, List.map_map, List.countP_map]
  apply List.map_congr_left
  intro x hx
  dsimp
  congr 1
  apply List.countP_congr
  intro a ha
  simpa using order a ha x hx

theorem occurs_trans {p q w : List ℕ} (hp : occurs p q) (hq : occurs q w) :
    occurs p w := by
  obtain ⟨z, sz, rfl⟩ := hq
  obtain ⟨v, sv, hv⟩ := hp
  obtain ⟨u, su, rfl⟩ := List.sublist_map_iff.mp sv
  refine ⟨u, su.trans sz, ?_⟩
  rw [standardize_map_of_order] at hv
  · exact hv
  · intro a ha b hb
    change 1 + z.countP (· < a) < 1 + z.countP (· < b) ↔ a < b
    constructor
    · intro h
      by_contra! h'
      have := below_mono z h'
      omega
    · intro h
      have := below_strict h z (su.subset ha)
      omega

/-- Count actual length-n permutations at a prescribed inversion count with the given extra basis. -/
def sourceCount (B : List (List ℕ)) (n k : ℕ) : ℕ :=
  (List.range n).permutations.countP fun w =>
    StableInversions.invCount w == k && ([1,3,2,4] :: B).all (fun p => !(occursB p w))

def diagonalDifference (B : List (List ℕ)) (d : ℤ) (n : ℕ) : ℤ :=
  let k := ((n : ℤ) + d).toNat
  (sourceCount B (n+1) k : ℤ) - (sourceCount B n k : ℤ)

def EventuallyAffine (f : ℕ → ℤ) (s : ℤ) : Prop :=
  ∃ t : ℤ, ∃ N : ℕ, ∀ n ≥ N, f n = s * (n : ℤ) + t

def EventuallyConstant (f : ℕ → ℤ) : Prop :=
  ∃ t : ℤ, ∃ N : ℕ, ∀ n ≥ N, f n = t

theorem affine_difference {f : ℕ → ℤ} {s : ℤ} (h : EventuallyAffine f s) :
    ∃ N : ℕ, ∀ n ≥ N, f (n+1) - f n = s := by
  obtain ⟨t, N, ht⟩ := h
  refine ⟨N, fun n hn => ?_⟩
  rw [ht n hn, ht (n+1) (by omega), Nat.cast_add, Nat.cast_one, Int.mul_add, Int.mul_one]
  omega

theorem affine_constant_iff {f : ℕ → ℤ} {s : ℤ} (h : EventuallyAffine f s) :
    EventuallyConstant f ↔ s=0 := by
  constructor
  · rintro ⟨t, M, hM⟩
    obtain ⟨N, hN⟩ := affine_difference h
    let n := max M N
    have eq := hN n (Nat.le_max_right _ _)
    rw [hM n (Nat.le_max_left _ _), hM (n+1) (by dsimp [n]; omega)] at eq
    omega
  · rintro rfl
    simpa [EventuallyAffine, EventuallyConstant] using h

theorem affine_add {f g : ℕ → ℤ} {s r : ℤ}
    (hf : EventuallyAffine f s) (hg : EventuallyAffine g r) :
    EventuallyAffine (fun n => f n + g n) (s+r) := by
  obtain ⟨t, N, hN⟩ := hf
  obtain ⟨u, M, hM⟩ := hg
  refine ⟨t+u, max N M, fun n hn => ?_⟩
  change f n + g n = _
  rw [hN n (by omega), hM n (by omega), Int.add_mul]
  omega

theorem affine_neg {f : ℕ → ℤ} {s : ℤ} (hf : EventuallyAffine f s) :
    EventuallyAffine (fun n => -f n) (-s) := by
  obtain ⟨t, N, hN⟩ := hf
  refine ⟨-t, N, fun n hn => ?_⟩
  change -f n = _
  rw [hN n hn, Int.neg_mul]
  omega

/-- Actual ordered pairs of allowed interval lengths whose sum is the specified length. -/
abbrev LengthPairs (u v n : ℕ) := {p : ℕ × ℕ // u ≤ p.1 ∧ v ≤ p.2 ∧ p.1+p.2=n}

def lengthPairEquiv (u v n : ℕ) (large : u+v≤n) :
    LengthPairs u v n ≃ Fin (n-u-v+1) where
  toFun p := ⟨p.1.1-u, by obtain ⟨⟨x,y⟩, hx, hy, hxy⟩ := p; dsimp at *; omega⟩
  invFun i := ⟨(u+i.val, n-(u+i.val)), by have hi := i.isLt; dsimp; omega⟩
  left_inv p := by
    obtain ⟨⟨x,y⟩, hx, hy, hxy⟩ := p
    apply Subtype.ext
    apply Prod.ext <;> dsimp at * <;> omega
  right_inv i := by apply Fin.ext; dsimp; omega

theorem two_interval_count (u v n : ℕ) (large : u+v≤n) :
    Nat.card (LengthPairs u v n) = n-u-v+1 := by
  rw [Nat.card_congr (lengthPairEquiv u v n large), Nat.card_fin]

theorem two_interval_slope (u v c : ℕ) :
    EventuallyAffine (fun n => (Nat.card (LengthPairs u v (n-c)) : ℤ)) 1 := by
  refine ⟨1-(u:ℤ)-v-c, u+v+c, fun n hn => ?_⟩
  change (Nat.card (LengthPairs u v (n-c)) : ℤ) = _
  rw [two_interval_count _ _ _ (by omega)]
  omega

/-- The signed affine and nonzero-slope tests stated on the original inversion numbers. -/
theorem source_tertiary_of_affine (B : List (List ℕ)) (d s : ℤ)
    (h : EventuallyAffine (diagonalDifference B d) s) :
    (∃ N : ℕ, ∀ n ≥ N, diagonalDifference B d (n+1) - diagonalDifference B d n = s) ∧
      (EventuallyConstant (diagonalDifference B d) ↔ s=0) :=
  ⟨affine_difference h, affine_constant_iff h⟩

end HigherInversionLimits
