module

public import SolvedMath.FoldedWords
public import SolvedMath.InducedIsomorphismStatement
public import Mathlib.Data.Finset.Interval

@[expose] public section

namespace FoldedLinearForests

open SimpleGraph BipartiteInducedIsomorphism
open scoped BigOperators

def Consecutive (u v : ℕ) : Prop := u+1 = v ∨ v+1 = u

structure LetterGraph (A : Type) where
  edge : A → A → Prop
  symmetric : ∀ {u v}, edge u v → edge v u

def foldGraph {A : Type} (w : ℕ → A) (K : LetterGraph A) : SimpleGraph ℕ where
  Adj u v := u ≠ v ∧ (Consecutive u v ↔ ¬ K.edge (w u) (w v))
  symm := ⟨by
    intro u v h
    obtain ⟨hn,he⟩ := h
    have h₁ : Consecutive v u ↔ Consecutive u v := or_comm
    have h₂ : K.edge (w v) (w u) ↔ K.edge (w u) (w v) := ⟨fun h => K.symmetric h,fun h => K.symmetric h⟩
    exact ⟨hn.symm,h₁.trans (he.trans (not_congr h₂.symm))⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

def foldedClass {A : Type} (w : ℕ → A) (K : LetterGraph A) : Set ListedGraph :=
  {G | Nonempty (G.graph ↪g foldGraph w K)}

def onesLoop : LetterGraph Bool where
  edge u v := u = true ∧ v = true
  symmetric := And.symm

noncomputable def slopeClass (a : ℝ) := foldedClass (letter a) onesLoop

section Recovery

variable {V : Type} [Fintype V] (f : V ↪ ℕ) (w : ℕ → Bool)

noncomputable def marked : Finset V := Finset.univ.filter (fun v => w (f v) = true)

noncomputable def neighbors (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun u => (foldGraph w onesLoop).Adj (f v) (f u))

private theorem degree_of_zero (v : V) (hz : w (f v) = false) :
    (neighbors f w v).card ≤ 2 := by
  classical
  have hin : (neighbors f w v).image f ⊆ {f v - 1, f v + 1} := by
    intro j hj
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hj
    have hw := (Finset.mem_filter.mp hu).2
    have hnear := hw.2.mpr (by simp [onesLoop,hz])
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hnear with h | h <;> omega
  have hnum := Finset.card_le_card hin
  rw [Finset.card_image_of_injective _ f.injective] at hnum
  have htwo := Finset.card_insert_le (f v - 1) ({f v+1} : Finset ℕ)
  simp only [Finset.card_singleton] at htwo
  omega

private theorem degree_of_one (v : V) (ho : w (f v) = true) :
    (marked f w).card ≤ (neighbors f w v).card + 3 := by
  classical
  let bad := marked f w \ neighbors f w v
  have hin : bad.image f ⊆ {f v - 1, f v, f v + 1} := by
    intro j hj
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hm,hn⟩ := Finset.mem_sdiff.mp hu
    have hu' := (Finset.mem_filter.mp hm).2
    have hna : ¬ (foldGraph w onesLoop).Adj (f v) (f u) := by
      intro h
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases he : f v = f u
    · exact Or.inr (Or.inl he.symm)
    · have hnear : Consecutive (f v) (f u) := by
        by_contra h
        exact hna ⟨he,by simp [onesLoop,ho,hu',h]⟩
      rcases hnear with h | h <;> omega
  have hnum := Finset.card_le_card hin
  rw [Finset.card_image_of_injective _ f.injective] at hnum
  have htwo := Finset.card_insert_le (f v) ({f v+1} : Finset ℕ)
  have hthree := Finset.card_insert_le (f v-1) ({f v,f v+1} : Finset ℕ)
  simp only [Finset.card_singleton] at htwo
  have hle : marked f w ⊆ bad ∪ neighbors f w v := by
    intro u hu
    by_cases hn : u ∈ neighbors f w v
    · exact Finset.mem_union_right _ hn
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hu,hn⟩)
  have hsum := Finset.card_union_le bad (neighbors f w v)
  have hc := Finset.card_le_card hle
  omega

/-- From six ones onward the uncolored induced graph determines every letter. -/
theorem degree_recovers_letters (many : 6 ≤ (marked f w).card) (v : V) :
    2 < (neighbors f w v).card ↔ w (f v) = true := by
  cases h : w (f v) with
  | false => simpa using degree_of_zero f w v h
  | true =>
    have := degree_of_one f w v h
    simp only [iff_true]
    omega

/-- Any other realization of the same finite adjacency data recovers the same marked set. -/
theorem two_representations (g : V ↪ ℕ) (v : ℕ → Bool)
    (many : 6 ≤ (marked f w).card)
    (same : ∀ i j, (foldGraph w onesLoop).Adj (f i) (f j) ↔
      (foldGraph v onesLoop).Adj (g i) (g j)) :
    ∀ i, w (f i) = v (g i) := by
  classical
  have hn (i : V) : neighbors f w i = neighbors g v i := by
    ext j
    simp only [neighbors, Finset.mem_filter,Finset.mem_univ,true_and,same]
  have sub : marked f w ⊆ marked g v := by
    intro i hi
    have h := (degree_recovers_letters f w many i).mpr (Finset.mem_filter.mp hi).2
    rw [hn] at h
    cases hv : v (g i)
    · have := degree_of_zero g v i hv
      omega
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
  have many' := many.trans (Finset.card_le_card sub)
  intro i
  have a := degree_recovers_letters f w many i
  have b := degree_recovers_letters g v many' i
  rw [hn] at a
  exact Bool.eq_iff_iff.mpr (a.symm.trans b)

end Recovery

end FoldedLinearForests
