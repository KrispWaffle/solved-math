module

public import SolvedMath.ClusterBeta
public import Mathlib.MeasureTheory.Integral.Pi

/-! An independent inverse-beta sample and its density on the unit interval. -/
@[expose] public section
namespace LeeSah
open MeasureTheory Set Function
open scoped unitInterval
noncomputable section

def betaMass (p q c : ℕ) : ℝ := ∫ t in (0:ℝ)..1, betaWeight p q c t

def normalizedBeta (p q c : ℕ) (x : I) : ℝ := betaWeight p q c x / betaMass p q c

lemma continuous_normalizedBeta (p q c : ℕ) : Continuous (normalizedBeta p q c) :=
  ((continuous_betaWeight p q c).comp continuous_subtype_val).div_const _

lemma normalizedBeta_nonneg (p q c : ℕ) (x : I) : 0 ≤ normalizedBeta p q c x :=
  div_nonneg (betaWeight_nonneg p q c x.property) (beta_mass_pos p q c).le

lemma integrable_normalizedBeta (p q c : ℕ) : Integrable (normalizedBeta p q c) volume :=
  integrableOn_univ.mp ((continuous_normalizedBeta p q c).continuousOn.integrableOn_compact isCompact_univ)

def betaLaw (p q c : ℕ) : Measure I := volume.map (betaIso p q c).symm

instance (p q c : ℕ) : IsProbabilityMeasure (betaLaw p q c) := by unfold betaLaw; infer_instance

lemma betaLaw_Iic (p q c : ℕ) (x : I) : betaLaw p q c (Iic x) = ENNReal.ofReal (betaCdf p q c x) := by
  let e := betaIso p q c
  have pre : e.symm ⁻¹' Iic x = Iic (e x) := by ext u; exact (e.symm_apply_le).trans Iff.rfl
  rw [betaLaw, Measure.map_apply e.symm.continuous.measurable measurableSet_Iic, pre,unitInterval.volume_Iic]
  rfl

lemma normalizedBeta_integral_Iic (p q c : ℕ) (x : I) :
    (∫ t in Iic x, normalizedBeta p q c t) = betaCdf p q c x := by
  unfold normalizedBeta betaCdf betaMass
  rw [integral_div,intervalIntegral.integral_of_le x.property.1,← integral_Icc_eq_integral_Ioc]
  congr 1
  have h := unitInterval.measurePreserving_coe.setIntegral_preimage_emb unitInterval.measurableEmbedding_coe
    (betaWeight p q c) (Iic (x:ℝ))
  have inter : Iic (x:ℝ) ∩ Icc (0:ℝ) 1 = Icc 0 (x:ℝ) := by
    ext t; simp only [mem_inter_iff,mem_Iic,mem_Icc]; exact ⟨fun w => ⟨w.2.1,w.1⟩,fun w => ⟨w.2,w.1,w.2.trans x.property.2⟩⟩
  rw [Measure.restrict_restrict measurableSet_Iic, inter] at h
  exact h

theorem betaLaw_density (p q c : ℕ) :
    betaLaw p q c = volume.withDensity (fun t : I => ENNReal.ofReal (normalizedBeta p q c t)) := by
  apply Measure.ext_of_Iic
  intro x
  rw [betaLaw_Iic,MeasureTheory.withDensity_apply _ measurableSet_Iic,← ofReal_integral_eq_lintegral_ofReal
    (integrable_normalizedBeta p q c).integrableOn (ae_of_all _ (normalizedBeta_nonneg p q c)),normalizedBeta_integral_Iic]

lemma betaLaw_real (p q c : ℕ) (S : Set I) (hS : MeasurableSet S) :
    (betaLaw p q c).real S = ∫ x in S, normalizedBeta p q c x := by
  rw [betaLaw_density,withDensity_real_apply _ hS, ← ofReal_integral_eq_lintegral_ofReal
    (integrable_normalizedBeta p q c).integrableOn (ae_of_all _ (normalizedBeta_nonneg p q c)),
    ENNReal.toReal_ofReal (integral_nonneg (normalizedBeta_nonneg p q c))]

lemma betaLaw_le_volume (p q c : ℕ) (S : Set I) (hS : MeasurableSet S) :
    (betaLaw p q c).real S ≤ volume.real S / betaMass p q c := by
  rw [betaLaw_real p q c S hS,← mul_one_div,← smul_eq_mul,← setIntegral_const]
  apply setIntegral_mono (integrable_normalizedBeta p q c).integrableOn (integrable_const _).integrableOn
  intro x
  exact div_le_div_of_nonneg_right (betaWeight_le_one p q c x.property) (beta_mass_pos p q c).le

end
end LeeSah
