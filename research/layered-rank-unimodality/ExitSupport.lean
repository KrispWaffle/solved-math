module

public import PeakPolynomial

@[expose] public section

namespace LayeredRanks
open Finset Polynomial
noncomputable section

private theorem embeds_left_self {u w : List ℕ} (h : Embeds u w) : Embeds u u := by
  induction h with
  | nil => exact .nil
  | cons ha _ ih => exact .cons ⟨ha.1, le_rfl⟩ ih
  | cons_right _ ih => exact ih

private theorem embeds_transitive {u v w : List ℕ} (h : Embeds u v) (h' : Embeds v w) :
    Embeds u w := by
  let : IsTrans ℕ (fun a b : ℕ => 0 < a ∧ a ≤ b) := ⟨fun _ _ _ hab hbc => ⟨hab.1, hab.2.trans hbc.2⟩⟩
  exact _root_.trans h h'

private theorem embeds_append_host {u w : List ℕ} (h : Embeds u w) (v : List ℕ) :
    Embeds u (w ++ v) := by
  induction h with
  | nil => exact .nil
  | cons ha _ ih => exact .cons ha ih
  | cons_right _ ih => exact .cons_right ih

theorem embeds_sum_le {u w : List ℕ} (h : Embeds u w) : u.sum ≤ w.sum := by
  induction h with
  | nil => simp
  | cons ha _ ih => simp only [List.sum_cons]; exact Nat.add_le_add ha.2 ih
  | cons_right _ ih => simp only [List.sum_cons]; omega

/-- Increase the weight by one inside the same ideal while retaining the starting word. -/
theorem embeds_raise_one {u w : List ℕ} (h : Embeds u w) (hw : ∀ a ∈ w, 0 < a)
    (lt : u.sum < w.sum) : ∃ v, Embeds u v ∧ Embeds v w ∧ v.sum = u.sum+1 := by
  induction w generalizing u with
  | nil => simp at lt
  | cons b w ih =>
    have hb := hw b (by simp)
    cases h with
    | nil => exact ⟨[1], .nil, .cons ⟨by decide, hb⟩ .nil, rfl⟩
    | cons_right hu => exact ⟨1::u, .cons_right (embeds_left_self hu), .cons ⟨by decide, hb⟩ hu, by simp [Nat.add_comm]⟩
    | @cons a _ u _ ha hu =>
      by_cases eq : a=b
      · have lt' : u.sum < w.sum := by simpa [eq] using lt
        obtain ⟨v, huv, hvw, he⟩ := ih hu (fun a h => hw a (by simp [h])) lt'
        exact ⟨a::v, .cons ⟨ha.1, le_rfl⟩ huv, .cons ha hvw, by simp [he, Nat.add_assoc]⟩
      · have hab : a+1 ≤ b := by have := ha.2; omega
        exact ⟨(a+1)::u, .cons ⟨ha.1, by omega⟩ (embeds_left_self hu), .cons ⟨by omega, hab⟩ hu,
          by simp only [List.sum_cons]; omega⟩

theorem exitPoly_eq_new_words (A : List ℕ) (M : ℕ) (bound : ∀ a ∈ A, a ≤ M) :
    exitPoly M A = wordPoly (subwords (A++[M]) \ subwords A) := by
  have hs : subwords A ⊆ subwords (A++[M]) := fun u hu => mem_subwords.2 (embeds_append_host (mem_subwords.1 hu) _)
  have parts : wordPoly (subwords (A++[M]) \ subwords A) + rankPoly A = rankPoly (A++[M]) :=
    Finset.sum_sdiff hs
  rw [rankPoly_append_max A M bound] at parts
  unfold exitPoly
  linear_combination -parts

private theorem wordPoly_coeff_card (T : Finset (List ℕ)) (r : ℕ) :
    (wordPoly T).coeff r = ((T.filter (fun u => u.sum=r)).card : ℤ) := by
  classical
  simp [wordPoly, coeff_X_pow, Finset.sum_boole, eq_comm]

theorem exitPoly_coeff_nonneg (A : List ℕ) (M r : ℕ) (bound : ∀ a ∈ A, a ≤ M) :
    0 ≤ (exitPoly M A).coeff r := by
  rw [exitPoly_eq_new_words _ _ bound, wordPoly_coeff_card]
  exact_mod_cast Nat.zero_le _

theorem exitPoly_coeff_pos_iff (A : List ℕ) (M r : ℕ) (bound : ∀ a ∈ A, a ≤ M) :
    0 < (exitPoly M A).coeff r ↔ ∃ u, Embeds u (A++[M]) ∧ ¬ Embeds u A ∧ u.sum = r := by
  classical
  rw [exitPoly_eq_new_words _ _ bound]
  rw [wordPoly_coeff_card]
  simp [Finset.card_pos, Finset.Nonempty, mem_subwords, and_assoc]

/-- Once an exit coefficient is positive, all degrees up to the full host weight occur. -/
theorem exitPoly_coeff_no_gaps (A : List ℕ) (M r s : ℕ) (hM : 0<M)
    (pos : ∀ a ∈ A, 0<a) (bound : ∀ a ∈ A, a ≤ M) (hr : 0 < (exitPoly M A).coeff r)
    (hrs : r ≤ s) (hs : s ≤ A.sum+M) : 0 < (exitPoly M A).coeff s := by
  induction s, hrs using Nat.le_induction with
  | base => exact hr
  | succ s _ ih =>
    obtain ⟨u, hu, hno, he⟩ := (exitPoly_coeff_pos_iff A M s bound).1 (ih (by omega))
    have lt : u.sum < (A++[M]).sum := by simp [he]; omega
    have positive : ∀ a ∈ A++[M], 0<a := by
      intro a h
      rcases List.mem_append.1 h with h | h
      · exact pos a h
      · simpa only [List.mem_singleton.1 h] using hM
    obtain ⟨v, huv, hv, ev⟩ := embeds_raise_one hu positive lt
    exact (exitPoly_coeff_pos_iff A M _ bound).2 ⟨v, hv, fun h => hno (embeds_transitive huv h), by omega⟩

private theorem embeds_common_prefix (A : List ℕ) {u w : List ℕ}
    (pos : ∀ a ∈ A, 0<a) (h : Embeds u w) : Embeds (A++u) (A++w) := by
  induction A with
  | nil => exact h
  | cons a A ih => exact .cons ⟨pos a (by simp), le_rfl⟩ (ih (fun t ht => pos t (by simp [ht])))

/-- The last M coefficients in the exit distribution are all strictly positive. -/
theorem exitPoly_top_coeffs (A : List ℕ) (M t : ℕ) (pos : ∀ a ∈ A, 0<a)
    (bound : ∀ a ∈ A, a ≤ M) (ht : 0<t) (htM : t≤M) :
    0 < (exitPoly M A).coeff (A.sum+t) := by
  apply (exitPoly_coeff_pos_iff _ _ _ bound).2
  refine ⟨A++[t], embeds_common_prefix A pos (.cons ⟨ht, htM⟩ .nil), ?_, by simp⟩
  intro h
  have bad := embeds_sum_le h
  simp at bad
  omega

end
end LayeredRanks
