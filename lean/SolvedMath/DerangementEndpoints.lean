module

public import SolvedMath.DerangementSpectrum
public import Mathlib.Order.Circular.ZMod
public import Mathlib.Order.Fin.Basic
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

namespace DerangementSpectrum

open Finset Filter
open scoped Topology
noncomputable section

private theorem increasing_perm_eq_refl {n : ℕ} (π : Perm n) (h : StrictMono π) :
    π = Equiv.refl _ := by
  let e : Fin n ≃o Fin n := ⟨π, h.le_iff_le⟩
  apply Equiv.ext
  intro i
  exact Fin.ext (Fin.coe_orderIso_apply e i)

def increasingClass : PermutationClass where
  slice n := {Equiv.refl (Fin n)}
  hereditary := by
    rintro m n π σ hπ ⟨pos, val, h⟩
    obtain rfl := Finset.mem_singleton.mp hπ
    apply Finset.mem_singleton.mpr
    apply increasing_perm_eq_refl
    intro a b hab
    apply val.lt_iff_lt.mp
    rw [← h a, ← h b]
    exact pos.strictMono hab

theorem zero_attained : Attained 0 := by
  refine ⟨increasingClass, fun n => ⟨Equiv.refl _, by simp [increasingClass]⟩, ?_⟩
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have h : Equiv.refl (Fin n) ∉ derangements (Fin n) := fun h => h ⟨0, hn⟩ rfl
  simp [ratio, free, total, increasingClass, filter_singleton, h]

private theorem sbtw_emb {m n : ℕ} (e : Fin m ↪o Fin n) (a b c : Fin m) :
    sbtw (e a) (e b) (e c) ↔ sbtw a b c := by
  simp [Fin.sbtw_iff]

/-- Hereditary class of permutations preserving the cyclic order of their points. -/
def cyclicClass : PermutationClass where
  slice n := by
    classical
    exact univ.filter (fun π : Perm n => ∀ a b c, sbtw a b c ↔ sbtw (π a) (π b) (π c))
  hereditary := by
    classical
    rintro m n π σ hπ ⟨pos, val, h⟩
    apply mem_filter.mpr
    refine ⟨mem_univ _, fun a b c => ?_⟩
    rw [← sbtw_emb pos a b c, (mem_filter.mp hπ).2, h, h, h, sbtw_emb]

private theorem sbtw_translate {n : ℕ} (k a b c : Fin (n+1)) :
    sbtw (a+k) (b+k) (c+k) ↔ sbtw a b c := by
  simp only [Fin.sbtw_iff, Fin.lt_def, Fin.val_add_eq_ite]
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hk := k.isLt
  split_ifs <;> omega

private theorem monotone_of_fixes_zero {n : ℕ} (π : Perm (n+1)) (hz : π 0 = 0)
    (hp : ∀ a b c, sbtw a b c ↔ sbtw (π a) (π b) (π c)) : StrictMono π := by
  intro i j hij
  have hj : j ≠ 0 := ne_of_gt (lt_of_le_of_lt (Fin.zero_le i) hij)
  have hj' : π j ≠ 0 := by rwa [← hz, π.injective.ne_iff]
  by_cases hi : i = 0
  · rw [hi, hz]
    exact lt_of_le_of_ne (Fin.zero_le _) hj'.symm
  have hi' : (0 : Fin (n+1)) < i := lt_of_le_of_ne (Fin.zero_le _) (Ne.symm hi)
  have h := (hp 0 i j).mp ((Fin.sbtw_iff).2 (Or.inl ⟨hi', hij⟩))
  simp [hz, Fin.sbtw_iff] at h
  exact h.2

def translate {n : ℕ} (k : Fin (n+1)) : Perm (n+1) := Equiv.addRight k

@[simp] private theorem translate_apply {n : ℕ} (k i : Fin (n+1)) :
    translate k i = i + k := rfl

private theorem translate_injective (n : ℕ) : Function.Injective (@translate n) := by
  intro i j h
  simpa using congrArg (fun π : Perm (n+1) => π 0) h

theorem cyclic_slice (n : ℕ) :
    cyclicClass.slice (n+1) = (univ : Finset (Fin (n+1))).image translate := by
  classical
  ext π
  constructor
  · intro h
    have hp := (mem_filter.mp h).2
    let k := π 0
    let f := π.trans (translate (-k))
    have hz : f 0 = 0 := by simp [f,k]
    have hf : ∀ a b c, sbtw a b c ↔ sbtw (f a) (f b) (f c) := by
      intro a b c
      simpa [f, sbtw_translate] using hp a b c
    have he := increasing_perm_eq_refl f (monotone_of_fixes_zero f hz hf)
    refine mem_image.mpr ⟨k, mem_univ _, ?_⟩
    apply Equiv.ext
    intro i
    have hh := congrArg (fun e : Perm (n+1) => e i) he
    change π i + -k = i at hh
    simpa [add_assoc] using (congrArg (fun x : Fin (n+1) => x + k) hh).symm
  · intro h
    obtain ⟨k, _, rfl⟩ := mem_image.mp h
    exact mem_filter.mpr ⟨mem_univ _, fun a b c => (sbtw_translate k a b c).symm⟩

theorem cyclic_counts (n : ℕ) :
    total cyclicClass (n+1) = n+1 ∧ free cyclicClass (n+1) = n := by
  classical
  have hfree (k : Fin (n+1)) : translate k ∈ derangements (Fin (n+1)) ↔ k ≠ 0 := by
    constructor
    · intro h e
      exact h 0 (by simp [e])
    · intro h i
      simpa using h
  constructor
  · simp [total, cyclic_slice, card_image_of_injective _ (translate_injective n)]
  · have eq : ((cyclicClass.slice (n+1)).filter (· ∈ derangements (Fin (n+1)))) =
        ((univ : Finset (Fin (n+1))).erase 0).image translate := by
      rw [cyclic_slice]
      ext π
      simp only [mem_filter, mem_image, mem_erase, mem_univ, true_and, and_true]
      constructor
      · rintro ⟨⟨k, rfl⟩, hk⟩
        exact ⟨k, (hfree k).mp hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨⟨k, rfl⟩, (hfree k).mpr hk⟩
    unfold free
    rw [eq, card_image_of_injective _ (translate_injective n), card_erase_of_mem (mem_univ _)]
    simp

theorem one_attained : Attained 1 := by
  classical
  refine ⟨cyclicClass, ?_, ?_⟩
  · intro n
    exact ⟨Equiv.refl _, mem_filter.mpr ⟨mem_univ _, fun _ _ _ => Iff.rfl⟩⟩
  · apply (tendsto_add_atTop_iff_nat 1).1
    have hz := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hl := (tendsto_const_nhds (x := (1:ℝ))).sub hz
    simp only [sub_zero] at hl
    apply hl.congr
    intro n
    rw [ratio, (cyclic_counts n).1, (cyclic_counts n).2]
    push_cast
    have hn : (n:ℝ)+1 ≠ 0 := by positivity
    field_simp
    ring

/-- The full attained set in the source, conditional on the two written finite-decoration
estimates. Zero and one use actual hereditary classes and require no hypotheses. -/
theorem attained_values_of_finite_decorations {lo hi : ℝ} (hlo : 0 ≤ lo) (horder : lo ≤ hi)
    (hbracket : ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∃ (F : PermutationClass) (M : ℕ),
      (∀ n > M, F.slice n = ∅) ∧ 0 < total F 0 ∧
      p ∈ Set.Icc (freeWeightRatio F M lo) (freeWeightRatio F M hi))
    (hattach : ∀ (F : PermutationClass) (M : ℕ), (∀ n > M, F.slice n = ∅) →
      0 < total F 0 → ∀ z ∈ Set.Icc lo hi, Attained (freeWeightRatio F M z)) :
    {p : ℝ | Attained p} = Set.Icc 0 1 := by
  classical
  ext p
  constructor
  · rintro ⟨C, hC, hlim⟩
    apply isClosed_Icc.mem_of_tendsto hlim
    apply Eventually.of_forall
    intro n
    have pos : (0:ℝ) < total C n := by
      exact_mod_cast Finset.card_pos.mpr (hC n)
    have sub : (free C n : ℝ) ≤ total C n := by
      exact_mod_cast (Finset.card_filter_le (C.slice n) (· ∈ derangements (Fin n)))
    exact ⟨div_nonneg (Nat.cast_nonneg _) pos.le, (div_le_one pos).2 sub⟩
  · exact source_spectrum_from_decoration_estimates hlo horder zero_attained one_attained
      hbracket hattach p

end
end DerangementSpectrum
