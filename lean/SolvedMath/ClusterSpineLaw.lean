module

public import SolvedMath.ClusterExtensionLaw
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp

/-! The marginal law of the spine after integrating the branches of the original poset. -/
@[expose] public section
namespace LeeSah
open Set MeasureTheory Function
open scoped unitInterval
noncomputable section

abbrev Spine (c n : ℕ) := Fin (n*c+1) → I
abbrev Rows (k n : ℕ) := Fin n → Fin k → I
abbrev rowLaw (k n : ℕ) := Measure.pi fun _ : Fin n => cube (Fin k)

def assemble (p q c n : ℕ) (v : Spine c n × Rows p n × Rows q n) : Element p q c n → I
  | .inl s => v.1 s
  | .inr (.inl (w,j)) => v.2.1 w j
  | .inr (.inr (w,j)) => v.2.2 w j

lemma measurable_assemble (p q c n : ℕ) : Measurable (assemble p q c n) := by
  apply measurable_pi_iff.mpr
  rintro (s | (⟨w,j⟩ | ⟨w,j⟩))
  · exact (measurable_pi_apply s).comp measurable_fst
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply w).comp (measurable_fst.comp measurable_snd))
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply w).comp (measurable_snd.comp measurable_snd))

lemma assemble_preserves (p q c n : ℕ) :
    MeasurePreserving (assemble p q c n)
      ((cube (Fin (n*c+1))).prod ((rowLaw p n).prod (rowLaw q n))) (cube (Element p q c n)) := by
  refine ⟨measurable_assemble p q c n,(Measure.pi_eq fun S hS => ?_).symm⟩
  rw [Measure.map_apply (measurable_assemble p q c n) (MeasurableSet.univ_pi hS)]
  have e : assemble p q c n ⁻¹' univ.pi S =
      univ.pi (fun s => S (.inl s)) ×ˢ
      (univ.pi (fun w => univ.pi fun j => S (.inr (.inl (w,j)))) ×ˢ
       univ.pi (fun w => univ.pi fun j => S (.inr (.inr (w,j))))) := by
    ext v
    simp [assemble, Sum.forall, Prod.forall]
  rw [e]
  simp only [Measure.prod_prod, Measure.pi_pi, Fintype.prod_sum_type, Fintype.prod_prod_type]

lemma measurable_legal (p q c n : ℕ) : MeasurableSet (legalLabels p q c n) := by
  unfold legalLabels Respects StrictMono
  simp only [Set.ofPred_and, Set.ofPred_forall]
  repeat' first | apply MeasurableSet.inter | apply MeasurableSet.iInter; intro
  all_goals exact measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _)

def markedWeight (p q c n : ℕ) (z : Spine c n) : ℝ :=
  ∏ w : Fin n, (z (mark c w.castSucc) : ℝ)^p * (1-(z (mark c w.succ):ℝ))^q

def branchFactor (p q n : ℕ) : ℝ := ((p.factorial:ℝ)*q.factorial)^n

lemma branchFactor_pos (p q n : ℕ) : 0 < branchFactor p q n := by
  unfold branchFactor
  positivity

private lemma real_pi_rows (k n : ℕ) (S : Fin n → Set (Fin k → I)) :
    (rowLaw k n).real (univ.pi S) = ∏ w, (cube (Fin k)).real (S w) := by
  simp only [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]

private lemma branch_fiber (p q c n : ℕ) (z : Spine c n) :
    let L := univ.pi fun w : Fin n => {r : Fin p → I | StrictMono r ∧ ∀ j, r j < z (mark c w.castSucc)}
    let U := univ.pi fun w : Fin n => {r : Fin q → I | StrictMono r ∧ ∀ j, z (mark c w.succ) < r j}
    ((rowLaw p n).prod (rowLaw q n)).real (L ×ˢ U) = markedWeight p q c n z / branchFactor p q n := by
  dsimp only
  rw [measureReal_prod_prod, real_pi_rows, real_pi_rows]
  apply (eq_div_iff (branchFactor_pos p q n).ne').2
  rw [← Finset.prod_mul_distrib]
  unfold markedWeight branchFactor
  rw [show ((p.factorial:ℝ)*q.factorial)^n = ∏ _ : Fin n, ((p.factorial:ℝ)*q.factorial) by simp,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro w _
  rw [← lower_chain_volume p (z (mark c w.castSucc)), ← upper_chain_volume q (z (mark c w.succ))]
  ring

/-- For any measurable event of the original spine, the exact marginal is its
ordered-spine integral with the marked weight and the branch factorials. -/
theorem spine_event_probability (p q c n : ℕ) (E : Set (Spine c n)) (hE : MeasurableSet E) :
    (cube (Element p q c n)).real (legalLabels p q c n ∩ {x | (fun s => x (.inl s)) ∈ E}) =
      (∫ z in cone (n*c+1) ∩ E, markedWeight p q c n z ∂cube (Fin (n*c+1))) / branchFactor p q n := by
  classical
  let A := legalLabels p q c n ∩ {x : Element p q c n → I | (fun s => x (.inl s)) ∈ E}
  let f := assemble p q c n
  let ν := (rowLaw p n).prod (rowLaw q n)
  let μ := cube (Fin (n*c+1))
  let C := cone (n*c+1) ∩ E
  have hA : MeasurableSet A := (measurable_legal p q c n).inter
    ((show Measurable (fun x : Element p q c n → I => fun s => x (Sum.inl s)) from
      measurable_pi_iff.mpr fun s => measurable_pi_apply (Sum.inl s)) hE)
  have hC : MeasurableSet C := (measurableCone _).inter hE
  have hfA := (measurable_assemble p q c n) hA
  have fiber (z : Spine c n) : ν.real (Prod.mk z ⁻¹' (f ⁻¹' A)) =
      C.indicator (fun v => markedWeight p q c n v / branchFactor p q n) z := by
    by_cases mem : z ∈ C
    · rw [Set.indicator_of_mem mem]
      have eqn : Prod.mk z ⁻¹' (f ⁻¹' A) =
          (univ.pi fun w : Fin n => {r : Fin p → I | StrictMono r ∧ ∀ j, r j < z (mark c w.castSucc)}) ×ˢ
          (univ.pi fun w : Fin n => {r : Fin q → I | StrictMono r ∧ ∀ j, z (mark c w.succ) < r j}) := by
        ext ⟨l,u⟩
        change (Respects (assemble p q c n (z,l,u)) ∧ z ∈ E) ↔ _
        simp only [Respects, assemble, mem_prod, mem_univ_pi, mem_ofPred_eq]
        exact ⟨fun h => ⟨fun w => ⟨h.1.2.1 w,h.1.2.2.2.1 w⟩, fun w => ⟨h.1.2.2.1 w,h.1.2.2.2.2 w⟩⟩,
          fun h => ⟨⟨mem.1,fun w => (h.1 w).1,fun w => (h.2 w).1,fun w => (h.1 w).2,
            fun w => (h.2 w).2⟩,mem.2⟩⟩
      rw [eqn]
      exact branch_fiber p q c n z
    · rw [Set.indicator_of_notMem mem]
      have e : Prod.mk z ⁻¹' (f ⁻¹' A) = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun ⟨l,u⟩ h =>
        mem ⟨h.1.1,h.2⟩
      rw [e,measureReal_empty]
  change (cube (Element p q c n)).real A = _
  rw [measureReal_def, ← (assemble_preserves p q c n).measure_preimage hA.nullMeasurableSet,
    Measure.prod_apply hfA, ← integral_toReal (measurable_measure_prodMk_left hfA).aemeasurable
      (ae_of_all _ fun _ => measure_lt_top _ _)]
  change (∫ z, ν.real (Prod.mk z ⁻¹' (f ⁻¹' A)) ∂μ) = _
  simp_rw [fiber]
  rw [integral_indicator hC,integral_div]

lemma measurable_labelBad (p q c n : ℕ) (η : ℝ) : MeasurableSet {z : Spine c n | labelBad p q c η z} := by
  unfold labelBad
  rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  exact measurableSet_lt measurable_const (show Measurable (fun z : Spine c n =>
    |(z (mark c i) : ℝ)-betaQuantile p q c (((i.val:ℝ)+1)/((n:ℝ)+2))|) by fun_prop)

/-- The branch factors cancel when conditioning on a legal extension. -/
theorem labelBadFraction_eq_spine (p q c n : ℕ) (η : ℝ) :
    labelBadFraction p q c n η =
      (∫ z in cone (n*c+1) ∩ {z : Spine c n | labelBad p q c η z},
        markedWeight p q c n z ∂cube (Fin (n*c+1))) /
      (∫ z in cone (n*c+1), markedWeight p q c n z ∂cube (Fin (n*c+1))) := by
  have den := spine_event_probability p q c n univ MeasurableSet.univ
  simp only [mem_univ, Set.ofPred_true, inter_univ] at den
  have num := spine_event_probability p q c n _ (measurable_labelBad p q c n η)
  simp only [mem_ofPred_eq] at num
  dsimp only [labelBadFraction]
  rw [num,den,div_div_div_cancel_right₀]
  exact (branchFactor_pos p q n).ne'

end
end LeeSah
