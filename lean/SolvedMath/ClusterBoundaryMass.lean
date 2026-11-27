module

public import SolvedMath.ClusterSpineBounds
public import Mathlib.Order.Fin.Tuple

/-! A polynomial lower bound for the normalizing integral. -/
@[expose] public section
namespace LeeSah
open MeasureTheory Set Function Filter
open scoped unitInterval
noncomputable section

lemma betaMass_le_one (p q c : ℕ) : betaMass p q c ≤ 1 := by
  have h := betaLaw_le_volume p q c univ MeasurableSet.univ
  simp only [probReal_univ] at h
  simpa only [one_mul] using (le_div_iff₀ (show 0 < betaMass p q c from beta_mass_pos p q c)).mp h

def margin (p q c N : ℕ) : ℝ := betaMass p q c / (8*N)

lemma margin_bounds (p q c N : ℕ) (hN : 0 < N) :
    0 < margin p q c N ∧ 4*margin p q c N ≤ 1 ∧
    (N:ℝ)*(4*margin p q c N/betaMass p q c) = 1/2 := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have nn : (N:ℝ) ≠ 0 := by linarith
  have hb : 0 < betaMass p q c := beta_mass_pos p q c
  unfold margin
  refine ⟨div_pos hb (by linarith),?_,?_⟩
  · rw [mul_div_assoc',div_le_one (by linarith)]
    linarith [betaMass_le_one p q c]
  · field_simp; norm_num

/-- Independent tail samples all avoid the boundary at once with probability
at least one half for the chosen margin. Ordering costs exactly a factorial. -/
theorem ref_safe_mass (p q c N : ℕ) (hN : 0 < N) :
    margin p q c N / 2 ≤ (N.factorial:ℝ)*(refLaw p q c N).real (safeSpine N (margin p q c N)) := by
  let r := margin p q c N
  obtain ⟨hr,hr4,tiny⟩ := margin_bounds p q c N hN
  change 0 < r at hr
  change 4*r ≤ 1 at hr4
  change (N:ℝ)*(4*r/betaMass p q c) = 1/2 at tiny
  let l : I := ⟨r,by constructor <;> linarith⟩
  let a : I := ⟨2*r,by constructor <;> linarith⟩
  let b : I := ⟨1-2*r,by constructor <;> linarith⟩
  let ν := betaLaw p q c
  let T := Ioo a b
  let e := (betaIso p q c).symm
  let S := e ⁻¹' T
  let B := {v : Fin N → I | StrictMono v ∧ ∀ j, v j ∈ S}
  let μ := (volume : Measure I).prod (cube (Fin N))
  have hcom : Tᶜ ⊆ Iic a ∪ Ici b := by
    intro t h
    by_cases h₁ : t ≤ a
    · exact Or.inl h₁
    · exact Or.inr (le_of_not_gt fun h₂ => h ⟨lt_of_not_ge h₁,h₂⟩)
  have hv₁ : volume.real (Iic a) = 2*r := by
    rw [measureReal_def,unitInterval.volume_Iic,ENNReal.toReal_ofReal a.property.1]
  have hv₂ : volume.real (Ici b) = 2*r := by
    rw [measureReal_def,unitInterval.volume_Ici,ENNReal.toReal_ofReal (sub_nonneg.mpr b.property.2)]
    dsimp [b]; ring
  have fail : 1-ν.real T ≤ 4*r/betaMass p q c := calc
    _ = ν.real Tᶜ := (probReal_compl_eq_one_sub measurableSet_Ioo).symm
    _ ≤ ν.real (Iic a) + ν.real (Ici b) := (measureReal_mono hcom).trans (measureReal_union_le _ _)
    _ ≤ (2*r)/betaMass p q c + (2*r)/betaMass p q c := by
      simpa only [hv₁,hv₂] using add_le_add (betaLaw_le_volume p q c (Iic a) measurableSet_Iic)
        (betaLaw_le_volume p q c (Ici b) measurableSet_Ici)
    _ = _ := by ring
  have each : (1/2:ℝ) ≤ (ν.real T)^N := by
    have pwr := one_add_mul_sub_le_pow (show -1 ≤ ν.real T by linarith [measureReal_nonneg (μ := ν) (s := T)]) N
    have low := mul_le_mul_of_nonneg_left fail (show 0 ≤ (N:ℝ) by positivity)
    linarith
  have mS : MeasurableSet S := e.continuous.measurable measurableSet_Ioo
  have vS : volume.real S = ν.real T :=
    congrArg ENNReal.toReal (Measure.map_apply e.continuous.measurable measurableSet_Ioo).symm
  have vv : (N.factorial:ℝ)*(cube (Fin N)).real B = (ν.real T)^N := by
    rw [← vS]
    exact sorted_in_region N S mS
  have inc : (Ioo l a ×ˢ B) ⊆ sampleSpine p q c N ⁻¹' safeSpine N r := by
    rintro ⟨u,v⟩ ⟨hu,hv⟩
    have obs (j : Fin N) : a < e (v j) ∧ e (v j) < b := hv.2 j
    have first : (u:ℝ) < 2*r := hu.2
    have all (j : Fin (N+1)) : (sampleSpine p q c N (u,v) j : ℝ) ≤ 1-r := by
      refine Fin.cases ?_ (fun k => ?_) j
      · change (u:ℝ) ≤ 1-r; linarith
      · have h : (e (v k):ℝ) < 1-2*r := (obs k).2
        change (e (v k):ℝ) ≤ 1-r; linarith
    exact ⟨Fin.strictMono_cons.2 ⟨fun k => hu.2.trans (obs k).1,e.strictMono.comp hv.1⟩,
      (show r < (u:ℝ) from hu.1).le,all _⟩
  have eqn := congrArg ENNReal.toReal ((sampleSpine_preserves p q c N).measure_preimage
    (measurable_safeSpine N r).nullMeasurableSet)
  change μ.real (sampleSpine p q c N ⁻¹' safeSpine N r) = (refLaw p q c N).real (safeSpine N r) at eqn
  have head : volume.real (Ioo l a) = r := by
    rw [measureReal_def,unitInterval.volume_Ioo]
    change (ENNReal.ofReal (2*r-r)).toReal = r
    rw [show 2*r-r=r by ring,ENNReal.toReal_ofReal hr.le]
  change r/2 ≤ _
  calc
    _ ≤ r*((ν.real T)^N) := by linarith [mul_le_mul_of_nonneg_left each hr.le]
    _ = (N.factorial:ℝ)*μ.real (Ioo l a ×ˢ B) := by rw [←vv,measureReal_prod_prod,head]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ((measureReal_mono inc).trans_eq eqn) (by positivity)

end
end LeeSah
