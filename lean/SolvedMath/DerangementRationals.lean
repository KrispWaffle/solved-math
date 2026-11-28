module

public import SolvedMath.DerangementBlocks
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

namespace DerangementSpectrum

open Finset Filter
open scoped Topology
noncomputable section

/-- Restrict a prefix of the host to selected positions. Its complementary suffix can only shrink. -/
private theorem restrict_cut {m n : ℕ} (pos : Fin m ↪o Fin n) (c : ℕ) :
    ∃ k ≤ m, m-k ≤ n-c ∧ ∀ i, (pos i).val < c ↔ i.val < k := by
  classical
  let s := (univ : Finset (Fin m)).filter (fun i => c ≤ (pos i).val)
  by_cases hs : s.Nonempty
  · let q := s.min' hs
    have hq : c ≤ (pos q).val := (mem_filter.mp (min'_mem s hs)).2
    let b : Fin n := ⟨c, lt_of_le_of_lt hq (pos q).isLt⟩
    have hcard := card_le_card_of_injOn (s := Ici q) (t := Ici b) pos
      (fun i hi => mem_Ici.mpr (le_trans (show b ≤ pos q from hq)
        (pos.monotone (mem_Ici.mp hi)))) pos.injective.injOn
    refine ⟨q.val, q.isLt.le, by simpa [b, Fin.card_Ici] using hcard, ?_⟩
    intro i
    constructor
    · intro h
      by_contra! bad
      exact h.not_ge (le_trans hq (show (pos q).val ≤ (pos i).val from pos.monotone bad))
    · intro h
      by_contra! bad
      have hmem : i ∈ s := mem_filter.mpr ⟨mem_univ _, bad⟩
      exact (not_le_of_gt h) (show q.val ≤ i.val from min'_le s i hmem)
  · refine ⟨m, le_rfl, by simp, fun i => iff_of_true ?_ i.isLt⟩
    by_contra! bad
    exact hs ⟨i, mem_filter.mpr ⟨mem_univ _, bad⟩⟩

/-- In a low tail an ascent requires its second position to lie in the prefix.
In a high tail it is enough for its first position to lie there. -/
def hasTail {n : ℕ} (low : Bool) (bound : ℕ) (π : Perm n) : Prop :=
  ∃ c ≤ n, n-c ≤ bound ∧ ∀ i j : Fin n, i < j →
    (π i < π j ↔ (if low then j.val else i.val) < c)

def tailClass (low : Bool) (bound : ℕ) : PermutationClass where
  slice n := by
    classical
    exact univ.filter (hasTail (n := n) low bound)
  hereditary := by
    classical
    rintro m n π σ hmem ⟨pos, val, eq⟩
    obtain ⟨c, _, hbound, horder⟩ := (mem_filter.mp hmem).2
    obtain ⟨k, hkm, hsize, hk⟩ := restrict_cut pos c
    refine mem_filter.mpr ⟨mem_univ _, k, hkm, hsize.trans hbound, fun i j hij => ?_⟩
    rw [← val.lt_iff_lt, ← eq, ← eq, horder _ _ (pos.strictMono hij)]
    cases low <;> simp [hk]

private def tailValue (low : Bool) (n t i : ℕ) : ℕ :=
  if low then if i < n-t then t+i else n-1-i
  else if i < n-t then i else n-t+(n-1-i)

private def tailInverse (low : Bool) (n t i : ℕ) : ℕ :=
  if low then if i < t then n-1-i else i-t
  else tailValue false n t i

private theorem tailValue_lt (low : Bool) {n t i : ℕ} (ht : t ≤ n) (hi : i < n) :
    tailValue low n t i < n := by
  cases low <;> simp [tailValue] <;> split_ifs <;> omega

private theorem tailInverse_lt (low : Bool) {n t i : ℕ} (hi : i < n) :
    tailInverse low n t i < n := by
  cases low <;> simp [tailInverse, tailValue] <;> split_ifs <;> omega

private def tailPerm (low : Bool) (n t : ℕ) (ht : t ≤ n) : Perm n where
  toFun i := ⟨tailValue low n t i.val, tailValue_lt low ht i.isLt⟩
  invFun i := ⟨tailInverse low n t i.val, tailInverse_lt low i.isLt⟩
  left_inv i := by
    apply Fin.ext
    change tailInverse low n t (tailValue low n t i.val) = i.val
    have hi := i.isLt
    cases low <;> simp [tailInverse, tailValue] <;> split_ifs <;> omega
  right_inv i := by
    apply Fin.ext
    change tailValue low n t (tailInverse low n t i.val) = i.val
    have hi := i.isLt
    cases low <;> simp [tailInverse, tailValue] <;> split_ifs <;> omega

private theorem tailPerm_lt {n t : ℕ} (low : Bool) (ht : t ≤ n) {i j : Fin n} (hij : i < j) :
    tailPerm low n t ht i < tailPerm low n t ht j ↔ (if low then j.val else i.val) < n-t := by
  change tailValue low n t i.val < tailValue low n t j.val ↔ _
  have hi := i.isLt
  have hj := j.isLt
  change i.val < j.val at hij
  cases low <;> simp [tailValue] <;> split_ifs <;> omega

private theorem same_ascents {n : ℕ} (π σ : Perm n)
    (h : ∀ i j, i < j → (π i < π j ↔ σ i < σ j)) : π = σ := by
  have hall (i j : Fin n) : π i < π j ↔ σ i < σ j := by
    rcases lt_trichotomy i j with hl | rfl | hg
    · exact h i j hl
    · simp
    · have e₁ := π.injective.ne hg.ne
      have e₂ := σ.injective.ne hg.ne
      have h' := h j i hg
      grind
  let e := π.symm.trans σ
  have mono : StrictMono e := by
    intro a b hab
    exact (hall (π.symm a) (π.symm b)).1 (by simpa using hab)
  let order : Fin n ≃o Fin n := ⟨e, mono.le_iff_le⟩
  apply Equiv.ext
  intro i
  have eq := Fin.coe_orderIso_apply order (π i)
  change (σ (π.symm (π i))).val = (π i).val at eq
  exact Fin.ext (by simpa using eq.symm)

private theorem tail_iff {n : ℕ} (low : Bool) (b : ℕ) (π : Perm n) :
    hasTail low b π ↔ ∃ t, ∃ ht : t ≤ n, t ≤ b ∧ π = tailPerm low n t ht := by
  constructor
  · rintro ⟨c, hc, hb, h⟩
    refine ⟨n-c, by omega, hb, same_ascents _ _ (fun i j hij => ?_)⟩
    rw [tailPerm_lt low _ hij, h i j hij]
    omega
  · rintro ⟨t, ht, hb, rfl⟩
    exact ⟨n-t, by omega, by omega, fun _ _ ij => tailPerm_lt low ht ij⟩

def classUnion (A B : PermutationClass) : PermutationClass where
  slice n := A.slice n ∪ B.slice n
  hereditary := by
    intro m n π σ h hp
    rcases mem_union.mp h with h | h
    · exact mem_union_left _ (A.hereditary h hp)
    · exact mem_union_right _ (B.hereditary h hp)

/-- At large lengths the skew family supplies `a` derangements; the direct family
supplies `k` permutations with fixed points, including the common identity. -/
def fractionClass (a k : ℕ) := classUnion (tailClass true a) (tailClass false k)

private theorem mem_fractionClass {a k n : ℕ} (π : Perm n) :
    π ∈ (fractionClass a k).slice n ↔ hasTail true a π ∨ hasTail false k π := by
  classical
  simp [fractionClass, classUnion, tailClass]

private theorem zero_tail (low : Bool) (n : ℕ) :
    tailPerm low n 0 (Nat.zero_le _) = Equiv.refl _ := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  cases low <;> simp [tailPerm, tailValue]

private theorem one_high_tail {n : ℕ} (h : 1 ≤ n) :
    tailPerm false n 1 h = Equiv.refl _ := by
  apply Equiv.ext
  intro i
  apply Fin.ext
  change tailValue false n 1 i.val = i.val
  have hi := i.isLt
  simp [tailValue]
  omega

private theorem first_tail (low : Bool) {n t : ℕ} (ht : t < n) :
    ((tailPerm low n t ht.le) ⟨0, by omega⟩).val = (if low then t else 0) := by
  cases low <;> simp [tailPerm, tailValue, show 0 < n-t by omega]

private theorem last_high_tail {n t : ℕ} (ht : 0 < t) (htn : t ≤ n) :
    ((tailPerm false n t htn) ⟨n-1, by omega⟩).val = n-t := by
  simp [tailPerm, tailValue, show ¬ n-1 < n-t by omega]

private def memberAt {a k n : ℕ} (hn : a+k < n) : Fin a ⊕ Fin k → Perm n
  | .inl i => tailPerm true n (i.val+1) (by have := i.isLt; omega)
  | .inr j => tailPerm false n (j.val+1) (by have := j.isLt; omega)

private theorem memberAt_injective {a k n : ℕ} (hn : a+k < n) : Function.Injective (memberAt hn) := by
  let first : Fin n := ⟨0, by omega⟩
  let last : Fin n := ⟨n-1, by omega⟩
  intro x y h
  have hf := congrArg (fun π : Perm n => (π first).val) h
  have hl := congrArg (fun π : Perm n => (π last).val) h
  rcases x with i | j <;> rcases y with i' | j'
  · have hi := i.isLt
    have hi' := i'.isLt
    rw [show (memberAt hn (.inl i) first).val = i.val+1 from first_tail true (by omega),
      show (memberAt hn (.inl i') first).val = i'.val+1 from first_tail true (by omega)] at hf
    exact congrArg Sum.inl (Fin.ext (by omega))
  · have hi := i.isLt
    have hj := j'.isLt
    rw [show (memberAt hn (.inl i) first).val = i.val+1 from first_tail true (by omega),
      show (memberAt hn (.inr j') first).val = 0 from first_tail false (by omega)] at hf
    omega
  · have hj := j.isLt
    have hi := i'.isLt
    rw [show (memberAt hn (.inr j) first).val = 0 from first_tail false (by omega),
      show (memberAt hn (.inl i') first).val = i'.val+1 from first_tail true (by omega)] at hf
    omega
  · have hj := j.isLt
    have hj' := j'.isLt
    rw [show (memberAt hn (.inr j) last).val = n-(j.val+1) from last_high_tail (by omega) (by omega),
      show (memberAt hn (.inr j') last).val = n-(j'.val+1) from last_high_tail (by omega) (by omega)] at hl
    exact congrArg Sum.inr (Fin.ext (by omega))

private theorem fraction_slice {a k n : ℕ} (hk : 0 < k) (hn : a+k < n) :
    (fractionClass a k).slice n = univ.image (memberAt hn) := by
  classical
  ext π
  rw [mem_fractionClass]
  constructor
  · rintro (h | h)
    · obtain ⟨t, ht, hb, rfl⟩ := (tail_iff _ _ _).1 h
      cases t with
      | zero =>
        refine mem_image.mpr ⟨.inr ⟨0,hk⟩, mem_univ _, ?_⟩
        simp [memberAt, zero_tail, one_high_tail]
      | succ t => exact mem_image.mpr ⟨.inl ⟨t, hb⟩, mem_univ _, rfl⟩
    · obtain ⟨t, ht, hb, rfl⟩ := (tail_iff _ _ _).1 h
      cases t with
      | zero =>
        refine mem_image.mpr ⟨.inr ⟨0,hk⟩, mem_univ _, ?_⟩
        simp [memberAt, zero_tail, one_high_tail]
      | succ t => exact mem_image.mpr ⟨.inr ⟨t, hb⟩, mem_univ _, rfl⟩
  · intro h
    obtain ⟨i, _, rfl⟩ := mem_image.mp h
    rcases i with i | j
    · exact Or.inl ((tail_iff _ _ _).2 ⟨i.val+1, by have := i.isLt; omega, i.isLt, rfl⟩)
    · exact Or.inr ((tail_iff _ _ _).2 ⟨j.val+1, by have := j.isLt; omega, j.isLt, rfl⟩)

private theorem low_deranged {n t : ℕ} (ht : 0 < t) (hn : 2*t < n) :
    tailPerm true n t (by omega) ∈ derangements (Fin n) := by
  intro i h
  have hv := congrArg Fin.val h
  change tailValue true n t i.val = i.val at hv
  have hi := i.isLt
  simp [tailValue] at hv
  split_ifs at hv <;> omega

private theorem high_has_fixed {n t : ℕ} (ht : t < n) :
    tailPerm false n t ht.le ∉ derangements (Fin n) := by
  intro h
  exact h ⟨0, by omega⟩ (Fin.ext (first_tail false ht))

theorem fractionClass_counts (a k n : ℕ) (hk : 0 < k) (hsize : 2*(a+k) < n) :
    total (fractionClass a k) n = a+k ∧ free (fractionClass a k) n = a := by
  classical
  have hn : a+k < n := by omega
  constructor
  · simp [total, fraction_slice hk hn, card_image_of_injective _ (memberAt_injective hn)]
  · let f (i : Fin a) := memberAt hn (.inl i)
    have inj : Function.Injective f := (memberAt_injective hn).comp Sum.inl_injective
    have eq : (((fractionClass a k).slice n).filter (· ∈ derangements (Fin n))) = univ.image f := by
      ext π
      rw [fraction_slice hk hn]
      simp only [mem_filter, mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨⟨i, rfl⟩, h⟩
        rcases i with i | j
        · exact ⟨i, rfl⟩
        · exact (high_has_fixed (show j.val+1 < n by have := j.isLt; omega) h).elim
      · rintro ⟨i, rfl⟩
        exact ⟨⟨.inl i, rfl⟩, low_deranged (Nat.succ_pos _) (by have := i.isLt; omega)⟩
    unfold free
    rw [eq, card_image_of_injective _ inj]
    simp

theorem rational_attained {a b : ℕ} (hab : a < b) : Attained ((a:ℝ)/b) := by
  classical
  let k := b-a
  have hk : 0 < k := by dsimp [k]; omega
  have hsum : a+k = b := by dsimp [k]; omega
  refine ⟨fractionClass a k, ?_, ?_⟩
  · intro n
    refine ⟨Equiv.refl _, (mem_fractionClass _).2 (Or.inr ?_)⟩
    exact (tail_iff false k _).2 ⟨0, Nat.zero_le _, Nat.zero_le _, (zero_tail false n).symm⟩
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (2*(a+k))] with n hn
    obtain ⟨h₁, h₂⟩ := fractionClass_counts a k n hk hn
    rw [ratio, h₂, h₁, hsum]

end
end DerangementSpectrum
