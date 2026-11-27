module

public import SolvedMath.ClusterBetaLaw
public import SolvedMath.ClusterSpineLaw

/-! The product law with one uniform coordinate and independent beta tail coordinates. -/
@[expose] public section
namespace LeeSah
open MeasureTheory Set Function
open scoped unitInterval
noncomputable section

/-- Product of continuous coordinate densities on the uniform cube. -/
private theorem pi_density {ι : Type*} [Fintype ι] (ν : ι → Measure I) [∀ i, IsProbabilityMeasure (ν i)]
    (w : ι → I → ℝ) (hw : ∀ i, Continuous (w i)) (hn : ∀ i x, 0 ≤ w i x)
    (law : ∀ i S, MeasurableSet S → (ν i).real S = ∫ x in S, w i x) :
    Measure.pi ν = (cube ι).withDensity (fun z => ENNReal.ofReal (∏ i, w i (z i))) := by
  have hc : Continuous (fun z : ι → I => ∏ i, w i (z i)) :=
    continuous_finsetProd _ (fun i _ => (hw i).comp (continuous_apply i))
  have hi : Integrable (fun z : ι → I => ∏ i, w i (z i)) (cube ι) :=
    integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)
  refine Measure.pi_eq fun S hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),← ofReal_integral_eq_lintegral_ofReal hi.integrableOn
    (ae_of_all _ (fun z => Finset.prod_nonneg (fun i _ => hn i (z i)))),
    Measure.restrict_pi_pi,integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg
      (fun i _ => integral_nonneg (hn i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [← law i (S i) (hs i),ofReal_measureReal]

def refMarginal (p q c : ℕ) {N : ℕ} (i : Fin (N+1)) : Measure I :=
  if i = 0 then volume else betaLaw p q c

instance (p q c : ℕ) {N : ℕ} (i : Fin (N+1)) : IsProbabilityMeasure (refMarginal p q c i) := by
  unfold refMarginal; split <;> infer_instance

def refLaw (p q c N : ℕ) := Measure.pi (@refMarginal p q c N)

def tailWeight (p q c : ℕ) {N : ℕ} (z : Fin (N+1) → I) : ℝ :=
  ∏ j : Fin N, betaWeight p q c (z j.succ)

private def refWeight (p q c : ℕ) {N : ℕ} (i : Fin (N+1)) (x : I) : ℝ :=
  if i = 0 then 1 else normalizedBeta p q c x

private lemma refWeight_prod (p q c N : ℕ) (z : Fin (N+1) → I) :
    (∏ i, refWeight p q c i (z i)) = tailWeight p q c z / (betaMass p q c)^N := by
  simp [Fin.prod_univ_succ, refWeight, tailWeight, normalizedBeta, Finset.prod_div_distrib]

theorem refLaw_real (p q c N : ℕ) (E : Set (Fin (N+1) → I)) (hE : MeasurableSet E) :
    (refLaw p q c N).real E = (∫ z in E, tailWeight p q c z ∂cube (Fin (N+1))) / (betaMass p q c)^N := by
  let w := @refWeight p q c N
  have hw (i) : Continuous (w i) := by
    change Continuous (fun x => if i = 0 then (1:ℝ) else normalizedBeta p q c x)
    by_cases h : i = 0
    · simp [h,continuous_const]
    · simpa [h] using continuous_normalizedBeta p q c
  have hn (i x) : 0 ≤ w i x := by
    unfold w refWeight
    split
    · exact zero_le_one
    · exact normalizedBeta_nonneg _ _ _ _
  have law (i : Fin (N+1)) (S : Set I) (hS : MeasurableSet S) :
      (refMarginal p q c i).real S = ∫ x in S, w i x := by
    by_cases h : i = 0
    · simp [refMarginal,w,refWeight,h]
    · simpa [refMarginal,w,refWeight,h] using betaLaw_real p q c S hS
  rw [refLaw,pi_density _ w hw hn law,withDensity_real_apply_eq_integral
    ((show Continuous (fun z : Fin (N+1) → I => ∏ i, w i (z i)) from
      continuous_finsetProd _ fun i _ => (hw i).comp (continuous_apply i)).measurable.ennreal_ofReal.aemeasurable)
    (ae_of_all _ (fun _ _ => ENNReal.ofReal_lt_top)) hE.nullMeasurableSet]
  simp_rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => hn i _),w,refWeight_prod]
  rw [integral_div]

def sampleSpine (p q c N : ℕ) (v : I × (Fin N → I)) : Fin (N+1) → I :=
  Fin.cons v.1 (fun j => (betaIso p q c).symm (v.2 j))

lemma sampleSpine_preserves (p q c N : ℕ) : MeasurePreserving (sampleSpine p q c N)
    ((volume : Measure I).prod (cube (Fin N))) (refLaw p q c N) := by
  let e := (betaIso p q c).symm
  have m : Measurable (sampleSpine p q c N) := by
    apply measurable_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_fst
    · exact e.continuous.measurable.comp ((measurable_pi_apply j).comp measurable_snd)
  refine ⟨m,(Measure.pi_eq fun S hS => ?_).symm⟩
  rw [Measure.map_apply m (MeasurableSet.univ_pi hS)]
  have pre : sampleSpine p q c N ⁻¹' univ.pi S =
      S 0 ×ˢ (univ.pi fun j : Fin N => e ⁻¹' S j.succ) := by
    ext ⟨t,v⟩
    simp only [mem_preimage,mem_univ_pi,mem_prod,sampleSpine,Fin.forall_fin_succ,Fin.cons_zero,Fin.cons_succ,e]
  rw [pre,Measure.prod_prod,Measure.pi_pi,Fin.prod_univ_succ]
  simp only [refMarginal,ite_true,Fin.succ_ne_zero,ite_false]
  congr 1
  exact Finset.prod_congr rfl fun j _ => (Measure.map_apply e.continuous.measurable (hS j.succ)).symm

end
end LeeSah
