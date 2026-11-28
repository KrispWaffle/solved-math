module

public import SolvedMath.FoldedGraphs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Real.Cardinality

@[expose] public section

namespace FoldedLinearForests

open SimpleGraph BipartiteInducedIsomorphism
open scoped BigOperators

def blockPositions (s n : ℕ) : Fin n ↪ ℕ where
  toFun i := s+i.val
  inj' := fun _ _ h => Fin.ext (Nat.add_left_cancel h)

private theorem walk_bounds {u : ℕ → ℕ} {n : ℕ}
    (step : ∀ i < n, Consecutive (u i) (u (i+1))) (i j : ℕ) (hi : i ≤ j) (hj : j ≤ n) :
    u i ≤ u j + (j-i) ∧ u j ≤ u i + (j-i) := by
  induction j,hi using Nat.le_induction with
  | base => simp
  | succ k h ih =>
    obtain ⟨h₁,h₂⟩ := ih (by omega)
    rcases step k (by omega) with v | v <;> omega

/-- An injective unit-step walk in the integer path visits one whole interval. -/
theorem image_of_consecutive {n : ℕ} (g : Fin (n+1) ↪ ℕ)
    (step : ∀ i j, i.val+1 = j.val → Consecutive (g i) (g j)) :
    ∃ s, Finset.univ.image g = Finset.univ.image (blockPositions s (n+1)) := by
  let S := Finset.univ.image g
  have hs : S.Nonempty := ⟨g 0, Finset.mem_image_of_mem g (Finset.mem_univ _)⟩
  let s := S.min' hs
  obtain ⟨m,_,hm⟩ := Finset.mem_image.mp (Finset.min'_mem S hs)
  let u (k : ℕ) := g ⟨min k n,by omega⟩
  have uk (i : Fin (n+1)) : u i = g i := by
    dsimp only [u]
    congr 1
    apply Fin.ext
    exact min_eq_left (by omega)
  have hop (k : ℕ) (h : k < n) : Consecutive (u k) (u (k+1)) := by
    apply step
    change min k n + 1 = min (k+1) n
    omega
  refine ⟨s,Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    have hmin : s ≤ g i := Finset.min'_le S _ hx
    have hmax : g i ≤ s+n := by
      change g i ≤ S.min' hs + n
      rw [← hm, ← uk i, ← uk m]
      rcases le_total i.val m.val with h | h
      · have hh := (walk_bounds hop i.val m.val h (by omega)).1
        omega
      · have hh := (walk_bounds hop m.val i.val h (by omega)).2
        omega
    let j : Fin (n+1) := ⟨g i - s,by omega⟩
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,show s + (g i - s) = g i by omega⟩
  · simp only [Finset.card_image_of_injective _ (blockPositions s (n+1)).injective,
      Finset.card_image_of_injective _ g.injective, le_refl]

private theorem marked_same_image {n : ℕ} (f g : Fin n ↪ ℕ) (w : ℕ → Bool)
    (h : Finset.univ.image f = Finset.univ.image g) : (marked f w).card = (marked g w).card := by
  classical
  have im (e : Fin n ↪ ℕ) : (marked e w).image e =
      (Finset.univ.image e).filter (fun x => w x = true) := by
    ext x
    simp [marked]
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,rfl⟩,hi⟩
    · rintro ⟨⟨i,rfl⟩,hi⟩
      exact ⟨i,hi,rfl⟩
  rw [← Finset.card_image_of_injective _ f.injective, im f, h, ← im g,
    Finset.card_image_of_injective _ g.injective]

theorem block_marked_discrepancy {a : ℝ} (ha : 0 < a) (hb : a < 1) (s n : ℕ) :
    |((marked (blockPositions s n) (letter a)).card : ℝ) - n*a| < 1 := by
  have card : ((marked (blockPositions s n) (letter a)).card : ℤ) =
      ∑ j ∈ Finset.range n, (if letter a (s+j) then (1 : ℤ) else 0) := by
    rw [marked, Finset.natCast_card_filter]
    exact Fin.sum_univ_eq_sum_range (fun j => if letter a (s+j) then (1 : ℤ) else 0) n
  have eqr : ((marked (blockPositions s n) (letter a)).card : ℝ) =
      ((∑ j ∈ Finset.range n, (if letter a (s+j) then (1 : ℤ) else 0) : ℤ) : ℝ) := by
    exact_mod_cast card
  rw [eqr]
  exact block_discrepancy ha hb s n

private theorem unfold_step {X Y K : Prop} (hx : X) (h : (X ↔ ¬K) ↔ (Y ↔ ¬K)) : Y := by
  tauto

/-- A folded block of one slope occurring at another gives a common integer frequency. -/
theorem common_frequency {a b : ℝ} (ha : 1/3 < a) (ha' : a < 2/3) (hb : 1/3 < b) (hb' : b < 2/3)
    (sub : slopeClass a ⊆ slopeClass b) (n : ℕ) (hn : 20 ≤ n) :
    ∃ m : ℕ, |(m : ℝ) - (n+1 : ℕ)*a| < 1 ∧ |(m : ℝ) - (n+1 : ℕ)*b| < 1 := by
  classical
  let f := blockPositions 0 (n+1)
  let G : ListedGraph := ⟨n+1,(foldGraph (letter a) onesLoop).comap f⟩
  have own : G ∈ slopeClass a := ⟨⟨f,Iff.rfl⟩⟩
  obtain ⟨e⟩ := sub own
  let g := e.toEmbedding
  have hsame (i j) : (foldGraph (letter a) onesLoop).Adj (f i) (f j) ↔
      (foldGraph (letter b) onesLoop).Adj (g i) (g j) := e.map_rel_iff.symm
  have h₁ := block_marked_discrepancy (by linarith : 0 < a) (by linarith : a < 1) 0 (n+1)
  have many : 6 ≤ (marked f (letter a)).card := by
    change 6 ≤ (marked (blockPositions 0 (n+1)) (letter a)).card
    have hnl : 20 ≤ (n : ℝ) := by exact_mod_cast hn
    push_cast at h₁
    have hx := (abs_lt.mp h₁).1
    by_contra! h
    have hm : ((marked (blockPositions 0 (n+1)) (letter a)).card : ℝ) ≤ 5 := by exact_mod_cast (show (marked (blockPositions 0 (n+1)) (letter a)).card ≤ 5 by omega)
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ)-20 by linarith) (show 0 ≤ a-1/3 by linarith)]
  have colors := two_representations f (letter a) g (letter b) many hsame
  have hstep (i j : Fin (n+1)) (hij : i.val+1 = j.val) : Consecutive (g i) (g j) := by
    have hu : i ≠ j := by intro h; subst j; omega
    have hfne := f.injective.ne hu
    have hgne := g.injective.ne hu
    have hnear : Consecutive (f i) (f j) := Or.inl (by simpa [f,blockPositions] using hij)
    have eq := hsame i j
    change (_ ∧ (Consecutive _ _ ↔ ¬ (_ = true ∧ _ = true))) ↔
      (_ ∧ (Consecutive _ _ ↔ ¬ (_ = true ∧ _ = true))) at eq
    rw [colors i, colors j] at eq
    exact unfold_step hnear ⟨fun h => (eq.mp ⟨hfne,h⟩).2,fun h => (eq.mpr ⟨hgne,h⟩).2⟩
  obtain ⟨s,hs⟩ := image_of_consecutive g hstep
  have hc : marked f (letter a) = marked g (letter b) := by
    ext i
    simp only [marked, Finset.mem_filter, Finset.mem_univ, true_and, colors]
  have hcard := marked_same_image g (blockPositions s (n+1)) (letter b) hs
  refine ⟨(marked f (letter a)).card,h₁,?_⟩
  rw [hc,hcard]
  exact block_marked_discrepancy (by linarith) (by linarith) s (n+1)

theorem slope_eq_of_subclass {a b : ℝ} (ha : 1/3 < a) (ha' : a < 2/3) (hb : 1/3 < b)
    (hb' : b < 2/3) (sub : slopeClass a ⊆ slopeClass b) : a = b := by
  by_contra h
  have hp : 0 < |a-b| := abs_pos.mpr (sub_ne_zero.mpr h)
  obtain ⟨k,hk⟩ := exists_nat_gt (2/|a-b|)
  have hk' := (div_lt_iff₀ hp).mp hk
  obtain ⟨m,ham,hbm⟩ := common_frequency ha ha' hb hb' sub (k+20) (by omega)
  push_cast at ham hbm
  obtain ⟨ha₁,ha₂⟩ := abs_lt.mp ham
  obtain ⟨hb₁,hb₂⟩ := abs_lt.mp hbm
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (by linarith)] at hk'
    nlinarith
  · rw [abs_of_nonneg (by linarith)] at hk'
    nlinarith

end FoldedLinearForests
