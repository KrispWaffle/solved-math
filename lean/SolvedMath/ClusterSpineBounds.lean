module

public import SolvedMath.ClusterReference

/-! Finite density comparison and concentration on the independent reference spine. -/
@[expose] public section
namespace LeeSah
open MeasureTheory Set Function Filter
open scoped unitInterval
noncomputable section

private def extendSpine {N : ℕ} (z : Fin (N+1) → I) (k : ℕ) : ℝ :=
  z ⟨min k N,Nat.lt_succ_of_le (min_le_right _ _)⟩

private lemma extendSpine_at {N : ℕ} (z : Fin (N+1) → I) (k : Fin (N+1)) :
    extendSpine z k.val = (z k : ℝ) := by
  simp [extendSpine, Nat.min_eq_left (Nat.le_of_lt_succ k.isLt)]

private lemma single_product (p q c n : ℕ) (z : ℕ → ℝ) :
    sampleWeight p q c z n = ∏ j ∈ Finset.range (n*c), betaWeight p q c (z (j+1)) := by
  induction n with
  | zero => simp [sampleWeight]
  | succ n ih =>
    rw [Nat.succ_mul, Finset.prod_range_add]
    simpa only [sampleWeight,Finset.prod_range_succ] using
      congrArg (fun x => x * ∏ j ∈ Finset.range c, betaWeight p q c (z (n*c+j+1))) ih

private lemma finite_weights (p q c n : ℕ) (z : Spine c n) :
    spineWeight p q c (extendSpine z) n = markedWeight p q c n z ∧
    sampleWeight p q c (extendSpine z) n = tailWeight p q c z := by
  constructor
  · unfold spineWeight markedWeight
    rw [← Fin.prod_univ_eq_prod_range]
    apply Finset.prod_congr rfl
    intro w _
    rw [show w.val*c = (mark c w.castSucc).val from rfl, show (w.val+1)*c = (mark c w.succ).val from rfl,
      extendSpine_at,extendSpine_at]
  · rw [single_product,← Fin.prod_univ_eq_prod_range]
    unfold tailWeight
    exact Finset.prod_congr rfl fun j _ => congrArg _ (extendSpine_at z j.succ)

lemma tailWeight_nonneg (p q c N : ℕ) (z : Fin (N+1) → I) : 0 ≤ tailWeight p q c z :=
  Finset.prod_nonneg fun j _ => betaWeight_nonneg p q c (z j.succ).property

lemma markedWeight_nonneg (p q c n : ℕ) (z : Spine c n) : 0 ≤ markedWeight p q c n z :=
  Finset.prod_nonneg fun _ _ => mul_nonneg (pow_nonneg (z _).property.1 _)
    (pow_nonneg (sub_nonneg.mpr (z _).property.2) _)

lemma integrable_markedWeight (p q c n : ℕ) : Integrable (markedWeight p q c n) (cube (Fin (n*c+1))) := by
  have cont : Continuous (markedWeight p q c n) := by unfold markedWeight; fun_prop
  exact integrableOn_univ.mp (cont.continuousOn.integrableOn_compact isCompact_univ)

lemma integrable_tailWeight (p q c N : ℕ) : Integrable (@tailWeight p q c N) (cube (Fin (N+1))) := by
  have cont : Continuous (@tailWeight p q c N) := continuous_finsetProd _ fun j _ =>
    (continuous_betaWeight p q c).comp (continuous_subtype_val.comp (continuous_apply j.succ))
  exact integrableOn_univ.mp (cont.continuousOn.integrableOn_compact isCompact_univ)

theorem finite_density_sandwich (p q c n : ℕ) (hc : 0 < c) (z : Spine c n) (hz : StrictMono z) :
    markedWeight p q c n z ≤ tailWeight p q c z ∧
    (z 0 : ℝ)^p * (1-(z (Fin.last (n*c)):ℝ))^q * tailWeight p q c z ≤ markedWeight p q c n z := by
  let f := extendSpine z
  have mono : Monotone f := by
    intro i j h
    exact hz.monotone (show (min i (n*c)) ≤ min j (n*c) from min_le_min_right _ h)
  have unit (i) : f i ∈ Icc (0:ℝ) 1 := (z _).property
  have H := density_sandwich p q c hc f mono unit n
  obtain ⟨hw,ht⟩ := finite_weights p q c n z
  change spineWeight p q c f n = _ at hw
  change sampleWeight p q c f n = _ at ht
  rw [hw,ht] at H
  have e0 : f 0 = (z 0:ℝ) := extendSpine_at z 0
  have eN : f (n*c) = (z (Fin.last (n*c)):ℝ) := extendSpine_at z (Fin.last (n*c))
  rw [e0,eN] at H
  have a : (z (Fin.last (n*c)):ℝ)^p ≤ 1 := pow_le_one₀ (z _).property.1 (z _).property.2
  have b : (1-(z 0:ℝ))^q ≤ 1 := pow_le_one₀ (sub_nonneg.mpr (z 0).property.2) (by linarith [(z 0).property.1])
  have h₁ := mul_le_mul a b (pow_nonneg (sub_nonneg.mpr (z 0).property.2) q) zero_le_one
  refine ⟨H.1,H.2.trans ?_⟩
  simpa using mul_le_mul_of_nonneg_right h₁ (markedWeight_nonneg p q c n z)

def safeSpine (N : ℕ) (r : ℝ) : Set (Fin (N+1) → I) :=
  cone (N+1) ∩ {z | r ≤ (z 0 : ℝ) ∧ (z (Fin.last N):ℝ) ≤ 1-r}

lemma measurable_safeSpine (N : ℕ) (r : ℝ) : MeasurableSet (safeSpine N r) := by
  apply (measurableCone _).inter
  rw [Set.ofPred_and]
  exact (measurableSet_le measurable_const (measurable_subtype_coe.comp (measurable_pi_apply 0))).inter
    (measurableSet_le (measurable_subtype_coe.comp (measurable_pi_apply (Fin.last N))) measurable_const)

lemma safe_density_lower (p q c n : ℕ) (hc : 0 < c) {r : ℝ} (hr : 0 ≤ r)
    (z : Spine c n) (hz : z ∈ safeSpine (n*c) r) :
    r^(p+q) * tailWeight p q c z ≤ markedWeight p q c n z := by
  rw [pow_add]
  apply le_trans _ (finite_density_sandwich p q c n hc z hz.1).2
  apply mul_le_mul_of_nonneg_right _ (tailWeight_nonneg _ _ _ _ z)
  exact mul_le_mul (pow_le_pow_left₀ hr hz.2.1 _) (pow_le_pow_left₀ hr (by linarith [hz.2.2]) _)
    (pow_nonneg hr _) (pow_nonneg (z 0).property.1 _)

/-- The bad reference event observes all tail coordinates in the beta CDF scale. -/
def referenceBad (p q c N : ℕ) (η : ℝ) : Set (Fin (N+1) → I) :=
  {z | ∃ j : Fin N, η < |betaCdf p q c (z j.succ)-((j.val:ℝ)+1)/N|}

lemma measurable_referenceBad (p q c N : ℕ) (η : ℝ) : MeasurableSet (referenceBad p q c N η) := by
  unfold referenceBad
  rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  apply measurableSet_lt measurable_const
  exact ((((continuous_betaCdf p q c).comp (continuous_subtype_val.comp (continuous_apply j.succ))).sub
    continuous_const).abs).measurable

/-- Only the tail coordinates are symmetrized. The first spine label is integrated independently. -/
theorem ref_bad_bound (p q c N : ℕ) (hN : 0 < N) (η : ℝ) (hη : 0 < η) :
    (N.factorial:ℝ) * (refLaw p q c N).real (cone (N+1) ∩ referenceBad p q c N η) ≤
      N * (2*Real.exp (-2*N*η^2)) := by
  let A := cone (N+1) ∩ referenceBad p q c N η
  let μ := (volume : Measure I).prod (cube (Fin N))
  have ha : MeasurableSet A := (measurableCone _).inter (measurable_referenceBad _ _ _ _ _)
  have inc : sampleSpine p q c N ⁻¹' A ⊆ univ ×ˢ (cone N ∩ meshBad N η) := by
    rintro ⟨u,v⟩ ⟨h,⟨j,hj⟩⟩
    have mono : StrictMono (sampleSpine p q c N (u,v)) := h
    refine ⟨trivial,fun i k hik => (betaIso p q c).symm.strictMono.lt_iff_lt.mp (mono (show i.succ < k.succ from Nat.succ_lt_succ hik)),j,?_⟩
    have e : betaCdf p q c (sampleSpine p q c N (u,v) j.succ) = (v j : ℝ) :=
      congrArg Subtype.val ((betaIso p q c).apply_symm_apply (v j))
    rwa [e] at hj
  have eqn := congrArg ENNReal.toReal ((sampleSpine_preserves p q c N).measure_preimage ha.nullMeasurableSet)
  change μ.real (sampleSpine p q c N ⁻¹' A) = (refLaw p q c N).real A at eqn
  change _ * (refLaw p q c N).real A ≤ _
  rw [←eqn]
  calc
    _ ≤ (N.factorial:ℝ) * μ.real (univ ×ˢ (cone N ∩ meshBad N η)) :=
      mul_le_mul_of_nonneg_left (measureReal_mono inc) (by positivity)
    _ = (cube (Fin N)).real {x | x ∘ Tuple.sort x ∈ meshBad N η} := by
      simp [μ,ordered_slice_mass N _ (measurable_meshBad N η)]
    _ ≤ _ := sorted_mesh_tail N hN η hη

end
end LeeSah
