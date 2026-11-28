module

public import SolvedMath.HigherInversionLimits

@[expose] public section

namespace HigherInversionLimits
open StableInversions (invCount)

/-- A cut across which all entries on the left are larger contributes all cross pairs. -/
theorem inversion_count_above (L R : List ℕ) (above : ∀ a ∈ L, ∀ b ∈ R, b<a) :
    invCount (L++R) = invCount L + invCount R + L.length * R.length := by
  induction L with
  | nil => simp [invCount]
  | cons a L ih =>
    have tail := ih (fun x hx => above x (by simp [hx]))
    have crosses : R.countP (· < a) = R.length := List.countP_eq_length.mpr
      (fun b hb => by simpa using above a (by simp) b hb)
    simp only [List.cons_append, invCount, List.countP_append, List.length_cons, Nat.succ_mul]
    rw [tail, crosses]
    omega

theorem inversion_count_below (L R : List ℕ) (below : ∀ a ∈ L, ∀ b ∈ R, a<b) :
    invCount (L++R) = invCount L + invCount R := by
  induction L with
  | nil => simp [invCount]
  | cons a L ih =>
    have tail := ih (fun x hx => below x (by simp [hx]))
    have crosses : R.countP (· < a) = 0 := List.countP_eq_zero.mpr (by
      intro b hb
      have := below a (by simp) b hb
      simp; omega)
    simp only [List.cons_append, invCount, List.countP_append]
    rw [tail, crosses]
    omega

/-- In a 132-avoider all values on the left of the maximum exceed every value on its right. -/
theorem maximum_separates (L R : List ℕ) (m : ℕ) (distinct : (L++m::R).Nodup)
    (largest : ∀ b ∈ R, b<m) (avoids : ¬ occurs [1,3,2] (L++m::R)) :
    ∀ a ∈ L, ∀ b ∈ R, b<a := by
  intro a ha b hb
  have ne : a≠b := by
    rintro rfl
    exact (List.nodup_append.mp distinct).2.2 a ha a (List.mem_cons_of_mem m hb) rfl
  by_contra! hn
  have hab : a<b := by omega
  have hbm := largest b hb
  have ham : a<m := by omega
  apply avoids
  refine ⟨[a,m,b], (List.singleton_sublist.mpr ha).append
    (.cons_cons _ (List.singleton_sublist.mpr hb)), ?_⟩
  simp [standardize, List.countP_cons, hab, hbm, ham, Nat.not_lt.mpr hab.le,
    Nat.not_lt.mpr hbm.le, Nat.not_lt.mpr ham.le]

theorem maximum_split_inversions (L R : List ℕ) (m : ℕ) (distinct : (L++m::R).Nodup)
    (left : ∀ a ∈ L, a<m) (right : ∀ b ∈ R, b<m)
    (avoids : ¬ occurs [1,3,2] (L++m::R)) :
    invCount (L++m::R) = invCount L + invCount R + (L.length+1)*R.length := by
  have cross := maximum_separates L R m distinct right avoids
  have hi := inversion_count_above (L++[m]) R (by
    intro a ha b hb
    rcases List.mem_append.mp ha with ha | ha
    · exact cross a ha b hb
    · have h : a=m := by simpa using ha
      exact h ▸ right b hb)
  have lo := inversion_count_below L [m] (by
    intro a ha b hb
    have h : b=m := by simpa using hb
    exact h ▸ left a ha)
  simpa [List.append_assoc, lo, invCount] using hi

/-- The product bound uses the literal inversion count, on a word whose right part is nonempty. -/
theorem maximum_split_excess (L R : List ℕ) (m e : ℕ) (distinct : (L++m::R).Nodup)
    (left : ∀ a ∈ L, a<m) (right : ∀ b ∈ R, b<m) (nonempty : 0<R.length)
    (avoids : ¬ occurs [1,3,2] (L++m::R))
    (budget : invCount (L++m::R) + 1 = (L++m::R).length+e) :
    e = invCount L + invCount R + L.length*(R.length-1) := by
  rw [maximum_split_inversions L R m distinct left right avoids] at budget
  simp only [List.length_append, List.length_cons] at budget
  have h : (R.length-1)+1=R.length := by omega
  have expand : (L.length+1)*R.length =
      L.length*(R.length-1)+R.length+L.length := by
    conv_lhs => rw [← h, Nat.mul_succ, Nat.succ_mul]
    omega
  omega

theorem maximum_split_large (L R : List ℕ) (m e : ℕ) (distinct : (L++m::R).Nodup)
    (left : ∀ a ∈ L, a<m) (right : ∀ b ∈ R, b<m) (nonempty : 0<R.length)
    (avoids : ¬ occurs [1,3,2] (L++m::R))
    (budget : invCount (L++m::R) + 1 = (L++m::R).length+e)
    (large : 2*e+2 < (L++m::R).length) : L=[] ∨ R.length=1 := by
  have ex := maximum_split_excess L R m e distinct left right nonempty avoids budget
  by_cases hl : L=[]
  · exact Or.inl hl
  · right
    have hL : 0<L.length := List.length_pos_iff.mpr hl
    by_contra! hr
    have hR : 0<R.length-1 := by omega
    have bl := Nat.le_mul_of_pos_right L.length hR
    have br := Nat.le_mul_of_pos_left (R.length-1) hL
    simp only [List.length_append, List.length_cons] at large
    omega

end HigherInversionLimits
