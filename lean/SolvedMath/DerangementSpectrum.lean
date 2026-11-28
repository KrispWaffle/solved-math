module

public import Mathlib.Combinatorics.Derangements.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Positivity

@[expose] public section

namespace DerangementSpectrum

open Finset Filter
open scoped Topology
noncomputable section

abbrev Perm (n : ℕ) := Equiv.Perm (Fin n)

/-- Two increasing embeddings of positions and values identify a classical pattern. -/
def Contains {m n : ℕ} (π : Perm n) (σ : Perm m) : Prop :=
  ∃ pos val : Fin m ↪o Fin n, ∀ i, π (pos i) = val (σ i)

structure PermutationClass where
  slice (n : ℕ) : Finset (Perm n)
  hereditary {m n : ℕ} {π : Perm n} {σ : Perm m} :
    π ∈ slice n → Contains π σ → σ ∈ slice m

def total (C : PermutationClass) (n : ℕ) : ℕ := (C.slice n).card

def free (C : PermutationClass) (n : ℕ) : ℕ := by
  classical
  exact ((C.slice n).filter (· ∈ derangements (Fin n))).card

def ratio (C : PermutationClass) (n : ℕ) : ℝ := (free C n : ℝ) / total C n

/-- Vatter's attained values, with the uniform measure on the distinct members of each length. -/
def Attained (p : ℝ) : Prop :=
  ∃ C : PermutationClass, (∀ n, (C.slice n).Nonempty) ∧ Tendsto (ratio C) atTop (𝓝 p)

/-- Direct sum on the original position and value orders. -/
def directSum {m n : ℕ} (π : Perm m) (σ : Perm n) : Perm (m + n) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr π σ)

/-- The positional blocks stay in place and their value blocks exchange order. -/
def skewSum {m n : ℕ} (π : Perm m) (σ : Perm n) : Perm (m + n) :=
  ((directSum π σ).trans finAddFlip).trans (finCongr (Nat.add_comm n m))

@[simp] theorem directSum_left {m n : ℕ} (π : Perm m) (σ : Perm n) (i : Fin m) :
    directSum π σ (Fin.castAdd n i) = Fin.castAdd n (π i) := by
  simp [directSum, Equiv.permCongr_apply]

@[simp] theorem directSum_right {m n : ℕ} (π : Perm m) (σ : Perm n) (i : Fin n) :
    directSum π σ (Fin.natAdd m i) = Fin.natAdd m (σ i) := by
  simp [directSum, Equiv.permCongr_apply]

@[simp] theorem skewSum_left_val {m n : ℕ} (π : Perm m) (σ : Perm n) (i : Fin m) :
    (skewSum π σ (Fin.castAdd n i)).val = n + (π i).val := by
  simp [skewSum, Nat.add_comm]

@[simp] theorem skewSum_right_val {m n : ℕ} (π : Perm m) (σ : Perm n) (j : Fin n) :
    (skewSum π σ (Fin.natAdd m j)).val = (σ j).val := by
  simp [skewSum]

theorem directSum_derangement_iff {m n : ℕ} (π : Perm m) (σ : Perm n) :
    directSum π σ ∈ derangements (Fin (m+n)) ↔
      π ∈ derangements (Fin m) ∧ σ ∈ derangements (Fin n) := by
  change (∀ i, directSum π σ i ≠ i) ↔ (∀ i, π i ≠ i) ∧ (∀ j, σ j ≠ j)
  constructor
  · intro h
    constructor
    · intro i hi
      exact h (Fin.castAdd n i) (by simp [hi])
    · intro j hj
      exact h (Fin.natAdd m j) (by simp [hj])
  · rintro ⟨hπ, hσ⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hπ j
    · simpa using hσ j

theorem skewSum_derangement_iff {m n : ℕ} (π : Perm m) (σ : Perm n) :
    skewSum π σ ∈ derangements (Fin (m+n)) ↔
      (∀ i, n + (π i).val ≠ i.val) ∧ (∀ j, (σ j).val ≠ m + j.val) := by
  change (∀ i, skewSum π σ i ≠ i) ↔ _
  constructor
  · intro h
    constructor
    · intro i hi
      exact h (Fin.castAdd n i) (Fin.ext (by simpa using hi))
    · intro j hj
      exact h (Fin.natAdd m j) (Fin.ext (by simpa using hj))
  · rintro ⟨hl, hr⟩ i
    refine Fin.addCases (fun j h => ?_) (fun j h => ?_) i
    · exact hl j (by simpa using congrArg Fin.val h)
    · exact hr j (by simpa using congrArg Fin.val h)

/-- Genuine skew factors with displacement shorter than the opposite block cannot have fixed points. -/
theorem skewSum_derangement_of_short_displacement {m n : ℕ} (π : Perm m) (σ : Perm n)
    (hl : ∀ i, i.val < n + (π i).val) (hr : ∀ j, (σ j).val < m + j.val) :
    skewSum π σ ∈ derangements (Fin (m+n)) :=
  (skewSum_derangement_iff π σ).2 ⟨fun i => (hl i).ne', fun j => (hr j).ne⟩

/-- A boundary after the first `k` positions is a direct cut when those positions also
carry exactly the smallest `k` values. The terminal boundary is included. -/
def CutAt {n : ℕ} (π : Perm n) (k : ℕ) : Prop :=
  k ≤ n ∧ ∀ i, (π i).val < k ↔ i.val < k

def SumIndecomposable {n : ℕ} (π : Perm n) : Prop :=
  ∀ k, 0 < k → k < n → ¬ CutAt π k

theorem skewSum_sumIndecomposable {m n : ℕ} (π : Perm m) (σ : Perm n)
    (hm : 0 < m) (hn : 0 < n) : SumIndecomposable (skewSum π σ) := by
  intro k hk hkn cut
  let first : Fin m := ⟨0, hm⟩
  let last : Fin n := ⟨n-1, by omega⟩
  have left := (cut.2 (Fin.castAdd n first)).2 (by simpa [first] using hk)
  have right := (cut.2 (Fin.natAdd m last)).1
  rw [skewSum_left_val] at left
  rw [skewSum_right_val] at right
  have hs := (σ last).isLt
  have hlast : m + (n-1) < k := right (by omega)
  omega

theorem directSum_first_cut {m n : ℕ} (π : Perm m) (σ : Perm n) (hm : 0 < m)
    (hπ : SumIndecomposable π) :
    IsLeast {k : ℕ | 0 < k ∧ CutAt (directSum π σ) k} m := by
  constructor
  · refine ⟨hm, by omega, ?_⟩
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simp
  · rintro k ⟨hk, hcut⟩
    by_contra! hkm
    apply hπ k hk hkm
    refine ⟨hkm.le, fun i => ?_⟩
    simpa using hcut.2 (Fin.castAdd n i)

theorem directSum_injective {m n : ℕ} {π π' : Perm m} {σ σ' : Perm n}
    (h : directSum π σ = directSum π' σ') : π = π' ∧ σ = σ' := by
  constructor
  · apply Equiv.ext
    intro i
    have he := congrArg (fun f : Perm (m+n) => f (Fin.castAdd n i)) h
    simpa using he
  · apply Equiv.ext
    intro i
    have he := congrArg (fun f : Perm (m+n) => f (Fin.natAdd m i)) h
    simpa using he

/-- Finite length-weighted mass for the counts of an actual decoration class. -/
def weight (counts : ℕ → ℕ) (M : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (M+1), (counts j : ℝ) * z^j

def freeWeightRatio (F : PermutationClass) (M : ℕ) (z : ℝ) : ℝ :=
  weight (free F) M z / weight (total F) M z

theorem weight_pos {counts : ℕ → ℕ} (h : 0 < counts 0) (M : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    0 < weight counts M z := by
  unfold weight
  apply Finset.sum_pos'
  · intro j _
    positivity
  · exact ⟨0, by simp, by simpa using (show (0:ℝ) < counts 0 by exact_mod_cast h)⟩

theorem continuous_weight (counts : ℕ → ℕ) (M : ℕ) : Continuous (weight counts M) := by
  unfold weight
  exact continuous_finsetSum _ (fun j _ => continuous_const.mul (continuous_id.pow j))

theorem freeWeightRatio_interpolate (F : PermutationClass) (M : ℕ) {lo hi p : ℝ}
    (hempty : 0 < total F 0) (hlo : 0 ≤ lo) (horder : lo ≤ hi)
    (hp : p ∈ Set.Icc (freeWeightRatio F M lo) (freeWeightRatio F M hi)) :
    ∃ z ∈ Set.Icc lo hi, freeWeightRatio F M z = p := by
  apply intermediate_value_Icc horder _ hp
  exact (continuous_weight _ _).continuousOn.div (continuous_weight _ _).continuousOn
    (fun z hz => (weight_pos hempty M (hlo.trans hz.1)).ne')

/-- Interpolation for the source classes, from the two finite-decoration estimates in the proof. -/
theorem source_spectrum_from_decoration_estimates {lo hi : ℝ} (hlo : 0 ≤ lo) (horder : lo ≤ hi)
    (hzero : Attained 0) (hone : Attained 1)
    (hbracket : ∀ p ∈ Set.Ioo (0 : ℝ) 1, ∃ (F : PermutationClass) (M : ℕ),
      (∀ n > M, F.slice n = ∅) ∧ 0 < total F 0 ∧
      p ∈ Set.Icc (freeWeightRatio F M lo) (freeWeightRatio F M hi))
    (hattach : ∀ (F : PermutationClass) (M : ℕ), (∀ n > M, F.slice n = ∅) →
      0 < total F 0 → ∀ z ∈ Set.Icc lo hi, Attained (freeWeightRatio F M z)) :
    ∀ p ∈ Set.Icc (0 : ℝ) 1, Attained p := by
  intro p hp
  obtain rfl | hp₀ := eq_or_lt_of_le hp.1
  · exact hzero
  obtain rfl | hp₁ := eq_or_lt_of_le hp.2
  · exact hone
  obtain ⟨F, M, hfin, hempty, h⟩ := hbracket p ⟨hp₀, hp₁⟩
  obtain ⟨z, hz, rfl⟩ := freeWeightRatio_interpolate F M hempty hlo horder h
  exact hattach F M hfin hempty z hz

end
end DerangementSpectrum
