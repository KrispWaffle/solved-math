import SolvedMath.HigherInversionComponents
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.List.Permutation
import Mathlib.Data.Finset.Prod

namespace PrincipalInversionMonotonicity

open StableInversions (invCount)

def triangular : Nat → Nat
  | 0 => 0
  | d + 1 => triangular d + d

theorem triangular_band (target : Nat) :
    ∃ d, 1 ≤ d ∧ triangular d ≤ target ∧ target < triangular (d + 1) := by
  induction target with
  | zero => exact ⟨1, by decide, by decide, by decide⟩
  | succ t ih =>
    obtain ⟨d, pos, lo, hi⟩ := ih
    by_cases stays : t + 1 < triangular (d + 1)
    · exact ⟨d, pos, by omega, stays⟩
    · refine ⟨d + 1, by omega, by omega, ?_⟩
      change t + 1 < triangular (d + 1) + (d + 1)
      omega

theorem twice_triangular (d : Nat) : 2 * triangular d + d = d * d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [triangular, Nat.succ_mul, Nat.mul_succ]
    omega

/-- Direct sum of decreasing blocks on the consecutive alphabet beginning at start. -/
def layered (start : Nat) : List Nat → List Nat
  | [] => []
  | d :: ds => (List.range' start d).reverse ++ layered (start + d) ds

theorem layered_permutation (ds : List Nat) (start : Nat) :
    (layered start ds).Perm (List.range' start ds.sum) := by
  induction ds generalizing start with
  | nil => simp [layered]
  | cons d ds ih =>
    simpa [layered] using
      (List.reverse_perm (List.range' start d)).append (ih (start + d))

theorem inversions_decreasing (start d : Nat) :
    invCount (List.range' start d).reverse = triangular d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [List.range'_1_concat, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      invCount]
    have allBelow : ((List.range' start d).reverse.countP (· < start + d)) = d := by
      have h : (List.range' start d).reverse.countP (· < start + d) =
          (List.range' start d).reverse.length := List.countP_eq_length.mpr (by
        intro a ha
        exact decide_eq_true (List.mem_range'_1.mp (List.mem_reverse.mp ha)).2)
      simpa using h
    rw [allBelow, ih, triangular]
    omega

theorem inversions_layered (ds : List Nat) (start : Nat) :
    invCount (layered start ds) = (ds.map triangular).sum := by
  induction ds generalizing start with
  | nil => rfl
  | cons d ds ih =>
    rw [layered, HigherInversionLimits.inversion_count_below, inversions_decreasing, ih]
    · rfl
    · intro a ha b hb
      have ha' := (List.mem_range'_1.mp (List.mem_reverse.mp ha)).2
      have hb' := (List.mem_range'_1.mp ((layered_permutation ds (start + d)).mem_iff.mp hb)).1
      omega

/-- A permutation of exactly the prescribed length realizes the requested inversion count
as a sum of decreasing blocks. Each block starts above all preceding blocks. -/
theorem exact_inversion_filler (target length : Nat)
    (room : 3 * (Nat.sqrt (2 * target) + 1) ≤ length) :
    ∃ ds : List Nat, ds.sum = length ∧
      (layered 0 ds).Perm (List.range' 0 length) ∧ invCount (layered 0 ds) = target := by
  obtain ⟨d, pos, lo, hi⟩ := triangular_band target
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  change triangular (t + 1) ≤ target at lo
  change target < triangular (t + 1) + (t + 1) at hi
  let remainder := target - triangular (t + 1)
  have remainderBound : remainder < t + 1 := by
    dsimp [remainder]
    omega
  have rootBound : t ≤ Nat.sqrt (2 * target) := by
    apply Nat.le_sqrt.mpr
    have h := twice_triangular (t + 1)
    simp only [Nat.succ_mul, Nat.mul_succ] at h
    omega
  let padding := length - (t + 1 + 2 * remainder)
  let ds := (t + 1) :: (List.replicate remainder 2 ++ List.replicate padding 1)
  have len : ds.sum = length := by
    simp only [ds, List.sum_cons, List.sum_append, List.sum_replicate_nat, Nat.mul_one]
    dsimp [padding]
    omega
  refine ⟨ds, len, len ▸ layered_permutation ds 0, ?_⟩
  rw [inversions_layered]
  simp only [ds, List.map_cons, List.sum_cons, List.map_append, List.map_replicate,
    List.sum_append, List.sum_replicate_nat]
  change triangular (t + 1) + (remainder * 1 + padding * 0) = target
  dsimp [remainder]
  omega

/-- Direct sum on zero-based rank words. -/
def directSum (u v : List Nat) := u ++ v.map (u.length + ·)

theorem inversions_shift (s : Nat) (w : List Nat) :
    invCount (w.map (s + ·)) = invCount w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp [invCount, ih, List.countP_map, Function.comp_def]

noncomputable def bucket (D : List Nat → Prop) (n j : Nat) : Finset (List Nat) := by
  classical
  exact (List.range' 0 n).permutations.toFinset.filter (fun w => D w ∧ invCount w = j)

theorem mem_bucket {D : List Nat → Prop} {n j : Nat} {w : List Nat} :
    w ∈ bucket D n j ↔ w.Perm (List.range' 0 n) ∧ D w ∧ invCount w = j := by
  classical
  simp [bucket, List.mem_permutations]

theorem combine_buckets {D : List Nat → Prop}
    (closed : ∀ u v, D u → D v → D (directSum u v)) {m n i j : Nat}
    {u v : List Nat} (hu : u ∈ bucket D m i) (hv : v ∈ bucket D n j) :
    directSum u v ∈ bucket D (m + n) (i + j) := by
  obtain ⟨pu, du, iu⟩ := mem_bucket.mp hu
  obtain ⟨pv, dv, iv⟩ := mem_bucket.mp hv
  have lu : u.length = m := by simpa using pu.length_eq
  refine mem_bucket.mpr ⟨?_, closed u v du dv, ?_⟩
  · have h := pu.append (pv.map (m + ·))
    have join : List.range' 0 m ++ List.range' m n = List.range' 0 (m + n) := by
      simpa only [Nat.zero_add] using @List.range'_append_1 0 m n
    simpa [directSum, lu, List.map_add_range', join] using h
  · rw [directSum, HigherInversionLimits.inversion_count_below, inversions_shift, iu, iv]
    intro a ha b hb
    have ba := (List.mem_range'_1.mp (pu.mem_iff.mp ha)).2
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    omega

/-- The numerical coefficients of any direct-sum-closed set of physical
permutations are supermultiplicative in length and inversion weight together. -/
theorem coefficient_product_le {D : List Nat → Prop}
    (closed : ∀ u v, D u → D v → D (directSum u v)) (m n i j : Nat) :
    (bucket D m i).card * (bucket D n j).card ≤ (bucket D (m + n) (i + j)).card := by
  classical
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun p => directSum p.1 p.2)
  · rintro ⟨u,v⟩ hp
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp hp
    exact combine_buckets closed hu hv
  · rintro ⟨u,v⟩ hp ⟨u',v'⟩ hp' heq
    have lu : u.length = m := by
      simpa using (mem_bucket.mp (Finset.mem_product.mp hp).1).1.length_eq
    have lu' : u'.length = m := by
      simpa using (mem_bucket.mp (Finset.mem_product.mp hp').1).1.length_eq
    change u ++ v.map (u.length + ·) = u' ++ v'.map (u'.length + ·) at heq
    have sameU := congrArg (List.take m) heq
    rw [List.take_left' lu, List.take_left' lu'] at sameU
    have sameV := congrArg (List.drop m) heq
    rw [List.drop_left' lu, List.drop_left' lu', lu, lu'] at sameV
    exact Prod.ext sameU (List.map_injective_iff.mpr (fun a b hab => Nat.add_left_cancel hab) sameV)

end PrincipalInversionMonotonicity
