module

public import SolvedMath.ClusterBoundaryMass
public import SolvedMath.ClusterGrid
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The concentration estimate for the original random linear extension and its limit shape. -/
@[expose] public section
namespace LeeSah
open MeasureTheory Set Filter
open scoped Topology unitInterval
noncomputable section

private lemma weighted_reference (p q c N : ℕ) (E : Set (Fin (N+1) → I)) (hE : MeasurableSet E) :
    (∫ z in E, tailWeight p q c z ∂cube (Fin (N+1))) =
      (refLaw p q c N).real E * (betaMass p q c)^N :=
  ((eq_div_iff (pow_ne_zero N (beta_mass_pos p q c).ne')).mp (refLaw_real p q c N E hE)).symm

/-- The weighted-spine bound is uniform in every mark of the original poset. -/
theorem label_tail (p q c : ℕ) (hc : 0 < c) (η : ℝ) (hη : 0 < η) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ᶠ n : ℕ in atTop,
      let N := n*c
      labelBadFraction p q c n η ≤ 2*(N*(2*Real.exp (-2*N*ξ^2))) / (margin p q c N)^(p+q+1) := by
  obtain ⟨ξ,hξ,grid⟩ := labelBad_implies_reference p q c hc η hη
  refine ⟨ξ,hξ,?_⟩
  filter_upwards [grid,eventually_ge_atTop 1] with n inc hn
  let N := n*c
  let μ := cube (Fin (N+1))
  let ν := refLaw p q c N
  let W := markedWeight p q c n
  let H := @tailWeight p q c N
  let L := cone (N+1)
  let A := L ∩ {z : Spine c n | labelBad p q c η z}
  let D := L ∩ referenceBad p q c N ξ
  let r := margin p q c N
  let S := safeSpine N r
  let F : ℝ := N.factorial
  let b := (betaMass p q c)^N
  let T : ℝ := N*(2*Real.exp (-2*N*ξ^2))
  have hN : 0 < N := Nat.mul_pos hn hc
  have hr : 0 < r := (margin_bounds p q c N hN).1
  have hb : 0 < b := pow_pos (beta_mass_pos p q c) N
  have hF : 0 < F := by dsimp [F]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have ma : MeasurableSet A := (measurableCone _).inter (measurable_labelBad _ _ _ _ _)
  have md : MeasurableSet D := (measurableCone _).inter (measurable_referenceBad _ _ _ _ _)
  have ms : MeasurableSet S := measurable_safeSpine _ _
  have hw : Integrable W μ := integrable_markedWeight p q c n
  have hh : Integrable H μ := integrable_tailWeight p q c N
  have num : (∫ z in A, W z ∂μ) ≤ T/F*b := calc
    _ ≤ ∫ z in A, H z ∂μ := setIntegral_mono_on hw.integrableOn hh.integrableOn ma
      (fun z hz => (finite_density_sandwich p q c n hc z hz.1).1)
    _ ≤ ∫ z in D, H z ∂μ := setIntegral_mono_set hh.integrableOn
      (ae_of_all _ (tailWeight_nonneg p q c N)) (ae_of_all _ inc)
    _ = ν.real D*b := weighted_reference p q c N D md
    _ ≤ _ := mul_le_mul_of_nonneg_right ((le_div_iff₀ hF).2
      (by rw [mul_comm (ν.real D) F]; exact ref_bad_bound p q c N hN ξ hξ)) hb.le
  have den : r/2/F*b*r^(p+q) ≤ ∫ z in L, W z ∂μ := calc
    _ ≤ ν.real S*b*r^(p+q) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr.le _)
      apply mul_le_mul_of_nonneg_right _ hb.le
      apply (div_le_iff₀ hF).2
      simpa only [mul_comm] using ref_safe_mass p q c N hN
    _ = ∫ z in S, r^(p+q)*H z ∂μ := by
      rw [integral_const_mul,show (∫ z in S, H z ∂μ) = ν.real S*b from weighted_reference p q c N S ms]
      ring
    _ ≤ ∫ z in S, W z ∂μ := setIntegral_mono_on (hh.const_mul _).integrableOn hw.integrableOn ms
      (safe_density_lower p q c n hc hr.le)
    _ ≤ _ := setIntegral_mono_set hw.integrableOn (ae_of_all _ (markedWeight_nonneg p q c n))
      (ae_of_all _ fun _ hz => hz.1)
  rw [labelBadFraction_eq_spine]
  change (∫ z in A, W z ∂μ) / (∫ z in L, W z ∂μ) ≤ 2*T/r^(p+q+1)
  calc
    _ ≤ (T/F*b)/(r/2/F*b*r^(p+q)) :=
      div_le_div₀ (mul_nonneg (div_nonneg hT hF.le) hb.le) num (by positivity) den
    _ = _ := by rw [pow_succ]; field_simp

private lemma absorb_polynomial (k : ℕ) (a : ℝ) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, (N:ℝ)^k * Real.exp (-2*a*N) ≤ Real.exp (-a*N) := by
  have conv := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k:ℝ) a ha).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [conv.eventually_le_const zero_lt_one] with N h
  change (N:ℝ)^(k:ℝ)*Real.exp (-a*N) ≤ 1 at h
  rw [Real.rpow_natCast] at h
  have add : -2*a*N = (-a*N)+(-a*N) := by ring
  rw [add,Real.exp_add,←mul_assoc]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- An exponentially small tail for the original finite fraction of bad extensions. -/
theorem extension_rank_tail (p q c : ℕ) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ C κ : ℝ, 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      badFraction p q c n ε ≤ C*Real.exp (-κ*(n:ℝ)) := by
  let η := ε/2
  have hη : 0 < η := half_pos hε
  obtain ⟨ξ,hξ,bound⟩ := label_tail p q c hc η hη
  let k := p+q+1
  let B := betaMass p q c
  let A := 4*(8/B)^k
  let κ := min (ξ^2) (η^2)
  have hB : 0 < B := beta_mass_pos p q c
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hκ : 0 < κ := lt_min (sq_pos_of_pos hξ) (sq_pos_of_pos hη)
  refine ⟨A+2,κ,hκ,?_⟩
  have nN (n : ℕ) : n ≤ n*c := Nat.le_mul_of_pos_right n hc
  have nD (n : ℕ) : n ≤ Fintype.card (Element p q c n) := by
    rw [element_card]
    have h := Nat.le_mul_of_pos_left n (show 0 < p+q+c by omega)
    omega
  have ltN : Tendsto (fun n : ℕ => n*c) atTop atTop := tendsto_atTop_mono nN tendsto_id
  have ltD : Tendsto (fun n : ℕ => Fintype.card (Element p q c n)) atTop atTop :=
    tendsto_atTop_mono nD tendsto_id
  filter_upwards [bound, ltN.eventually (absorb_polynomial (k+1) (ξ^2) (sq_pos_of_pos hξ)),
    ltD.eventually (absorb_polynomial 1 (η^2) (sq_pos_of_pos hη)),eventually_ge_atTop 1] with n lab poly mesh hn
  let N := n*c
  let d := Fintype.card (Element p q c n)
  have hN : (0:ℝ) < N := by exact_mod_cast Nat.mul_pos hn hc
  have conv_exp {x y a : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (ha : κ ≤ a) :
      Real.exp (-a*y) ≤ Real.exp (-κ*x) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul,neg_le_neg_iff] using
      (show -(a*y) ≤ -(κ*x) from neg_le_neg (mul_le_mul ha hxy hx (hκ.le.trans ha)))
  have eN := conv_exp (x := (n:ℝ)) (y := (N:ℝ)) (by positivity) (by exact_mod_cast nN n)
    (min_le_left (ξ^2) (η^2))
  have ed := conv_exp (x := (n:ℝ)) (y := (d:ℝ)) (by positivity) (by exact_mod_cast nD n)
    (min_le_right (ξ^2) (η^2))
  have lab' : labelBadFraction p q c n η ≤ A * Real.exp (-κ*n) := by
    change _ ≤ 2*((N:ℝ)*(2*Real.exp (-2*N*ξ^2)))/(margin p q c N)^k at lab
    calc
      _ ≤ _ := lab
      _ = A*((N:ℝ)^(k+1)*Real.exp (-2*ξ^2*N)) := by
        change 2*((N:ℝ)*(2*Real.exp (-2*N*ξ^2)))/(B/(8*N))^k = 4*(8/B)^k*_
        rw [show -2*(N:ℝ)*ξ^2 = -2*ξ^2*N by ring]
        simp only [div_pow,mul_pow,pow_succ]
        field_simp
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (poly.trans eN) hA
  have mesh' : (d:ℝ)*(2*Real.exp (-2*d*η^2)) ≤ 2*Real.exp (-κ*n) := by
    change (d:ℝ)^1 * Real.exp (-2*η^2*d) ≤ Real.exp (-(η^2)*d) at mesh
    rw [pow_one] at mesh
    have e : -2*(d:ℝ)*η^2 = -2*η^2*d := by ring
    rw [e]
    linarith [mesh.trans ed]
  have transfer := rank_bound_of_labels p q c n η hη
  have e : 2*η = ε := by dsimp [η]; ring
  rw [e] at transfer
  exact transfer.trans ((add_le_add lab' mesh').trans_eq (by ring))

private lemma badFraction_le_one (p q c n : ℕ) (ε : ℝ) : badFraction p q c n ε ≤ 1 := by
  let S := {e : Ranking p q c n // IsExtension e ∧ rankBad ε e}
  let f (x : S) : Ext p q c n := ⟨x.val,x.property.1⟩
  have hf : Function.Injective f := fun _ _ h => Subtype.ext (congrArg (fun v : Ext p q c n => v.val) h)
  have h := Nat.card_le_card_of_injective f hf
  apply (div_le_one (show 0 < (Nat.card (Ext p q c n):ℝ) by exact_mod_cast extension_count_pos p q c n)).2
  exact_mod_cast h

/-- Positive constants giving an exponential bound for every stack size,
including the finitely many sizes before the asymptotic estimate takes effect. -/
theorem extension_rank_tail_all (p q c : ℕ) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ n : ℕ,
      badFraction p q c n ε ≤ C*Real.exp (-κ*(n:ℝ)) := by
  obtain ⟨C,κ,hκ,h⟩ := extension_rank_tail p q c hc ε hε
  obtain ⟨s,hs⟩ := eventually_atTop.1 h
  let C' := max C (Real.exp (κ*s))
  refine ⟨C',κ,(Real.exp_pos _).trans_le (le_max_right _ _),hκ,fun n => ?_⟩
  by_cases large : s ≤ n
  · exact (hs n large).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · calc
      _ ≤ 1 := badFraction_le_one p q c n ε
      _ ≤ Real.exp (κ*s)*Real.exp (-κ*n) := by
        rw [←Real.exp_add,Real.one_le_exp_iff]
        have le : (n:ℝ) ≤ s := by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge large))
        linarith [mul_le_mul_of_nonneg_left le hκ.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- Lee and Sah, Conjecture 6.1, simultaneously in every marked rank for all
admissible endpoints of the original chain stack. -/
theorem lee_sah_conjecture61 : Conjecture61 := by
  apply conjecture61_of_tail_bound
  intro m a b _ hab _ ε hε
  exact extension_rank_tail (a-1) (m-b) (b-a) (Nat.sub_pos_of_lt hab) ε hε

end
end LeeSah
