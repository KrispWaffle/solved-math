import SliceCurvature

namespace PrincipalPatternRanks

open DistinctPermutationPatterns
noncomputable section

/-- Relative gap in binomial log-concavity, uniform even near the endpoints. -/
theorem binomial_curvature (n j : ℕ) (hj : j+2≤n) :
    (1+4/(n:ℝ))*((n.choose j:ℝ)*(n.choose (j+2):ℝ)) ≤ (n.choose (j+1):ℝ)^2 := by
  have hz : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hjr : (j:ℝ)+2≤n := by exact_mod_cast hj
  have positive0 : 0<(n:ℝ)-j := by linarith
  have positive2 : 0<(j:ℝ)+2 := by positivity
  have left : (n.choose (j+1):ℝ)*((j:ℝ)+1)=(n.choose j:ℝ)*((n:ℝ)-j) := by
    have z := congrArg (fun x : ℕ => (x:ℝ)) (Nat.choose_succ_right_eq n j)
    push_cast [Nat.cast_sub (show j≤n by omega)] at z
    exact z
  have right : (n.choose (j+2):ℝ)*((j:ℝ)+2)=(n.choose (j+1):ℝ)*((n:ℝ)-j-1) := by
    have z := congrArg (fun x : ℕ => (x:ℝ)) (Nat.choose_succ_right_eq n (j+1))
    push_cast [Nat.cast_sub (show j+1≤n by omega)] at z
    linarith
  have solve0 := (eq_div_iff positive0.ne').mpr left.symm
  have solve2 := (eq_div_iff positive2.ne').mpr right
  have scalar : (1+4/(n:ℝ))*(((j:ℝ)+1)/((n:ℝ)-j))*(((n:ℝ)-j-1)/((j:ℝ)+2)) ≤ 1 := by
    field_simp
    nlinarith [sq_nonneg ((n:ℝ)-2*((j:ℝ)+1))]
  rw [solve0,solve2]
  calc
    _ = (n.choose (j+1):ℝ)^2 *
      ((1+4/(n:ℝ))*(((j:ℝ)+1)/((n:ℝ)-j))*(((n:ℝ)-j-1)/((j:ℝ)+2))) := by ring
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left scalar (sq_nonneg (n.choose (j+1):ℝ))

/-- The source counts distinct standardized patterns of one fixed length in the actual host. -/
def normalizedRank {n : ℕ} (π : Equiv.Perm (Fin n)) (m : ℕ) : ℝ :=
  (fixedSizeCount π m:ℝ)/(n.choose m:ℝ)

/-- A curvature margin for the normalized rank sequence forces strict log-concavity
of the literal distinct-pattern counts, including both neighbors of the middle rank. -/
theorem source_rank_log_concavity {n j : ℕ} (π : Equiv.Perm (Fin n)) (hj : j+2≤n)
    (h : normalizedRank π j * normalizedRank π (j+2) <
      (1+4/(n:ℝ))*(normalizedRank π (j+1))^2) :
    fixedSizeCount π j * fixedSizeCount π (j+2) < (fixedSizeCount π (j+1))^2 := by
  have positive (m : ℕ) (hm : m≤n) : 0<(n.choose m:ℝ) := by
    exact_mod_cast Nat.choose_pos hm
  have weight (m : ℕ) (hm : m≤n) :
      (fixedSizeCount π m:ℝ)=normalizedRank π m*(n.choose m:ℝ) := by
    rw [normalizedRank,div_mul_cancel₀ _ (positive m hm).ne']
  have pairpos := mul_pos (positive j (by omega)) (positive (j+2) hj)
  have lower := mul_lt_mul_of_pos_right h pairpos
  have upper := mul_le_mul_of_nonneg_left (binomial_curvature n j hj)
    (sq_nonneg (normalizedRank π (j+1)))
  have actual : (fixedSizeCount π j:ℝ)*(fixedSizeCount π (j+2):ℝ) <
      (fixedSizeCount π (j+1):ℝ)^2 := by
    rw [weight j (by omega),weight (j+2) hj,weight (j+1) (by omega)]
    linarith
  exact_mod_cast actual

/-- Vatter's source property for one finite host, with a possibly flat peak. -/
def RankUnimodal {n : ℕ} (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ peak ≤ n, (∀ i < peak, fixedSizeCount π i ≤ fixedSizeCount π (i+1)) ∧
    ∀ i, peak ≤ i → i<n → fixedSizeCount π (i+1) ≤ fixedSizeCount π i

/-- Upper-rank strict log-concavity joins the increasing initial ranks at their first fall. -/
theorem source_unimodal_of_curvature {n k : ℕ} (π : Equiv.Perm (Fin n))
    (initial : ∀ i<k, fixedSizeCount π i ≤ fixedSizeCount π (i+1))
    (curvature : ∀ j, k≤j → j+2≤n → normalizedRank π j * normalizedRank π (j+2) <
      (1+4/(n:ℝ))*(normalizedRank π (j+1))^2) : RankUnimodal π := by
  classical
  let D := fixedSizeCount π
  by_cases fall : ∃ i, i<n ∧ D (i+1)<D i
  · let peak := Nat.find fall
    obtain ⟨hn,hd⟩ : peak<n ∧ D (peak+1)<D peak := Nat.find_spec fall
    have hkp : k≤peak := by
      by_contra! early
      exact (not_lt_of_ge (initial peak early)) hd
    refine ⟨peak,hn.le,?_,?_⟩
    · intro j hj
      exact le_of_not_gt (fun h => Nat.find_min fall hj ⟨by omega,h⟩)
    · intro j hj
      obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hj
      induction d with
      | zero => intro _; exact hd.le
      | succ d ih =>
        intro top
        have previous := ih (by omega) (by omega)
        have lc := source_rank_log_concavity π (show peak+d+2≤n by omega)
          (curvature (peak+d) (by omega) (by omega))
        change D (peak+d)*D (peak+d+2)<(D (peak+d+1))^2 at lc
        change D (peak+d+2) ≤ D (peak+d+1)
        by_contra! rising
        exact (not_le_of_gt lc) (by simpa only [pow_two] using Nat.mul_le_mul previous rising.le)
  · refine ⟨n,le_rfl,?_,fun i hi top => by omega⟩
    intro i hi
    exact le_of_not_gt (fun h => fall ⟨i,hi,h⟩)

end
end PrincipalPatternRanks

/-- info: 'PrincipalPatternRanks.source_rank_log_concavity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrincipalPatternRanks.source_rank_log_concavity

/-- info: 'PrincipalPatternRanks.source_unimodal_of_curvature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrincipalPatternRanks.source_unimodal_of_curvature
