module

public import SolvedMath.ClusterOrderStatistics
public import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Ring

/-! Uniform continuous labels, sorted coordinates and volumes of chain constraints. -/
@[expose] public section
namespace LeeSah
open Set Filter MeasureTheory ProbabilityTheory Function
open scoped unitInterval
noncomputable section

abbrev cube (α : Type*) [Fintype α] : Measure (α → I) := Measure.pi (fun _ : α => (volume : Measure I))

def cone (n : ℕ) : Set (Fin n → I) := {x | StrictMono x}

theorem measurableCone (n : ℕ) : MeasurableSet (cone n) := by
  have e : cone n = ⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), {x : Fin n → I | x i < x j} := by
    ext x; simp [cone, StrictMono]
  rw [e]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)

def chamberSlice {α : Type*} {n : ℕ} (e : α ≃ Fin n) (B : Set (Fin n → I)) : Set (α → I) :=
  (fun x => x ∘ e.symm) ⁻¹' (cone n ∩ B)

lemma reorder_preserves {α : Type*} [Fintype α] {n : ℕ} (e : α ≃ Fin n) :
    MeasurePreserving (fun x : α → I => x ∘ e.symm) (cube α) (cube (Fin n)) := by
  have H := measurePreserving_piCongrLeft (α := fun _ : Fin n => I) (fun _ => volume) e
  convert H using 1
  funext x j
  obtain ⟨i,rfl⟩ := e.surjective j
  simp [MeasurableEquiv.piCongrLeft_apply_apply]

lemma chamber_disjoint {α : Type*} {n : ℕ} {e f : α ≃ Fin n} (ne : e ≠ f)
    (B C : Set (Fin n → I)) : Disjoint (chamberSlice e B) (chamberSlice f C) := by
  apply Set.disjoint_left.mpr
  intro x he hf
  have m1 : StrictMono (x ∘ e.symm) := he.1
  have m2 : StrictMono (x ∘ f.symm) := hf.1
  have m : StrictMono (fun j => e (f.symm j)) := by
    intro i j h
    apply m1.lt_iff_lt.mp
    simpa using m2 h
  apply ne
  apply Equiv.ext
  intro a
  simpa using m.apply_eq (x := f a)

/-- Every selected strict order receives the same share of a measurable event
specified through the sorted labels. -/
theorem selected_chambers {α S : Type*} [Fintype α] [Fintype S] {n : ℕ}
    (e : S → α ≃ Fin n) (distinct : Injective e) (B : Set (Fin n → I)) (hB : MeasurableSet B) :
    (cube α).real (⋃ s, chamberSlice (e s) B) = Fintype.card S * (cube (Fin n)).real (cone n ∩ B) := by
  have meas (s : S) : MeasurableSet (chamberSlice (e s) B) :=
    (reorder_preserves (e s)).measurable ((measurableCone n).inter hB)
  rw [measureReal_iUnion_fintype (fun _ _ h => chamber_disjoint (distinct.ne h) _ _) meas]
  have each (s : S) : (cube α).real (chamberSlice (e s) B) = (cube (Fin n)).real (cone n ∩ B) :=
    congrArg ENNReal.toReal ((reorder_preserves (e s)).measure_preimage
      ((measurableCone n).inter hB).nullMeasurableSet)
  simp [each]

/-- Distinct independent uniform labels give a strict total order almost surely. -/
lemma cube_injective (α : Type*) [Fintype α] : ∀ᵐ x ∂cube α, Injective x := by
  have ind : iIndepFun (fun (i : α) (x : α → I) => x i) (cube α) :=
    iIndepFun_pi (X := fun _ (v : I) => v) (fun _ => aemeasurable_id)
  have diag : ((volume : Measure I).prod volume) (diagonal I) = 0 := by
    rw [Measure.prod_apply measurableSet_diagonal]
    have sl (v : I) : (volume : Measure I) (Prod.mk v ⁻¹' diagonal I) = 0 := by
      have e : Prod.mk v ⁻¹' diagonal I = {v} := by ext y; simp [diagonal, eq_comm]
      simp [e]
    simp [sl]
  suffices h : ∀ᵐ x ∂cube α, ∀ i j, i ≠ j → x i ≠ x j from h.mono fun _ hw _ _ => not_imp_not.mp (hw _ _)
  refine ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => ?_
  by_cases h : i = j
  · simp [h]
  · have p := (ind.indepFun h).map_prod_eq_prod_map_map
        (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
    rw [(measurePreserving_eval (fun _ : α => (volume : Measure I)) i).map_eq,
      (measurePreserving_eval (fun _ : α => (volume : Measure I)) j).map_eq] at p
    have z := congrArg (fun μ : Measure (I × I) => μ (diagonal I)) p
    change (Measure.map (fun x : α → I => (x i,x j)) (cube α)) (diagonal I) =
      ((volume : Measure I).prod volume) (diagonal I) at z
    rw [Measure.map_apply (Measurable.prodMk (measurable_pi_apply i) (measurable_pi_apply j))
      (measurableSet_diagonal (α := I)), diag] at z
    have aeN : ∀ᵐ x ∂cube α, x i ≠ x j := by
      rw [ae_iff]
      convert z using 2
      ext x; simp [diagonal]
    exact aeN.mono fun _ hne _ => hne

/-- Sorting all n labels contributes the ordinary order-statistic law; the
chamber volume is the same for each of the n! possible rankings. -/
theorem ordered_slice_mass (n : ℕ) (B : Set (Fin n → I)) (hB : MeasurableSet B) :
    (n.factorial:ℝ) * (cube (Fin n)).real (cone n ∩ B) =
      (cube (Fin n)).real {x | x ∘ Tuple.sort x ∈ B} := by
  have mass := selected_chambers (α := Fin n) (S := Equiv.Perm (Fin n)) id injective_id B hB
  rw [Fintype.card_perm, Fintype.card_fin] at mass
  rw [← mass]
  apply measureReal_congr
  filter_upwards [cube_injective (Fin n)] with x hx
  change (x ∈ ⋃ e : Equiv.Perm (Fin n), chamberSlice e B) ↔ x ∘ Tuple.sort x ∈ B
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨e,he⟩
    have h : Monotone (x ∘ e.symm) := (show StrictMono (x ∘ e.symm) from he.1).monotone
    rw [← Tuple.comp_sort_eq_comp_iff_monotone.mpr h]
    exact he.2
  · intro h
    refine ⟨(Tuple.sort x).symm, ?_⟩
    change StrictMono (x ∘ Tuple.sort x) ∧ x ∘ Tuple.sort x ∈ B
    exact ⟨(Tuple.monotone_sort x).strictMono_of_injective (hx.comp (Tuple.sort x).injective), h⟩

lemma cone_mass (n : ℕ) : (n.factorial : ℝ) * (cube (Fin n)).real (cone n) = 1 := by
  simpa using ordered_slice_mass n univ MeasurableSet.univ

/-- Conditioning the cube on any nonempty family of rankings preserves the
entire distribution of sorted coordinates. -/
theorem sorted_law_given_rankings {α S : Type*} [Fintype α] [Fintype S] [Nonempty S] {n : ℕ}
    (e : S → α ≃ Fin n) (distinct : Injective e) (B : Set (Fin n → I)) (hB : MeasurableSet B) :
    (cube α).real (⋃ s, chamberSlice (e s) B) / (cube α).real (⋃ s, chamberSlice (e s) univ) =
      (cube (Fin n)).real {x | x ∘ Tuple.sort x ∈ B} := by
  rw [selected_chambers e distinct B hB, selected_chambers e distinct univ MeasurableSet.univ,
    Set.inter_univ, ← ordered_slice_mass n B hB]
  have cardPos : (0:ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  have pos : 0 < (cube (Fin n)).real (cone n) := by
    have h := cone_mass n
    have m := measureReal_nonneg (μ := cube (Fin n)) (s := cone n)
    by_contra! h0
    rw [le_antisymm h0 m, mul_zero] at h
    norm_num at h
  apply (div_eq_iff (mul_pos cardPos pos).ne').2
  calc
    _ = Fintype.card S * (cube (Fin n)).real (cone n ∩ B) * (n.factorial * (cube (Fin n)).real (cone n)) :=
      by rw [cone_mass, mul_one]
    _ = _ := by ring

/-- Integrating one chain constrained to a measurable region. This identity
also applies to a chain of size zero. -/
theorem sorted_in_region (n : ℕ) (S : Set I) (hs : MeasurableSet S) :
    (n.factorial:ℝ) * (cube (Fin n)).real {x | StrictMono x ∧ ∀ j, x j ∈ S} =
      (volume.real S)^n := by
  let B : Set (Fin n → I) := univ.pi (fun _ => S)
  have hB : MeasurableSet B := MeasurableSet.pi countable_univ (fun _ _ => hs)
  have H := ordered_slice_mass n B hB
  have e1 : cone n ∩ B = {x | StrictMono x ∧ ∀ j, x j ∈ S} := by ext x; simp [B, cone]
  have e2 : {x : Fin n → I | x ∘ Tuple.sort x ∈ B} = B := by
    ext x
    simp only [mem_ofPred_eq, B, mem_univ_pi, comp_apply]
    constructor
    · intro h j; obtain ⟨i,rfl⟩ := (Tuple.sort x).surjective j; exact h i
    · intro h i; exact h _
  rw [e1, e2] at H
  rw [H, measureReal_def]
  dsimp only [B]
  rw [Measure.pi_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.toReal_pow]
  rfl

lemma lower_chain_volume (n : ℕ) (u : I) :
    (n.factorial:ℝ) * (cube (Fin n)).real {x | StrictMono x ∧ ∀ j, x j < u} = (u:ℝ)^n := by
  simpa [measureReal_def, ENNReal.toReal_ofReal u.property.1] using sorted_in_region n (Iio u) measurableSet_Iio

lemma upper_chain_volume (n : ℕ) (u : I) :
    (n.factorial:ℝ) * (cube (Fin n)).real {x | StrictMono x ∧ ∀ j, u < x j} = (1-(u:ℝ))^n := by
  simpa [measureReal_def, ENNReal.toReal_ofReal (sub_nonneg.mpr u.property.2)] using
    sorted_in_region n (Ioi u) measurableSet_Ioi

end
end LeeSah
