module

public import SolvedMath.ClusterChambers
public import SolvedMath.ClusterHeight
import Mathlib.Tactic.Linarith

/-! Coupling a uniform linear extension of the original cluster poset with
uniform labels conditioned on the window inequalities. -/
@[expose] public section
namespace LeeSah
open Set Filter MeasureTheory Function
open scoped unitInterval
noncomputable section

abbrev Ext (p q c n : ℕ) := {e : Ranking p q c n // IsExtension e}

lemma respects_comp {p q c n : ℕ} {A B : Type*} [LinearOrder A] [Preorder B]
    (v : A → B) (hv : StrictMono v) (x : Element p q c n → A) :
    Respects (p := p) (q := q) (c := c) (n := n) (v ∘ x) ↔ Respects x := by
  simp only [Respects, StrictMono, comp_apply, hv.lt_iff_lt]

lemma respects_iff_rank {p q c n : ℕ} (x : Element p q c n → I) (e : Ranking p q c n)
    (h : StrictMono (x ∘ e.symm)) : Respects x ↔ IsExtension e := by
  have hv := respects_comp (p := p) (q := q) (c := c) (n := n) (x ∘ e.symm) h e
  simpa [IsExtension, Function.comp_assoc] using hv

lemma exists_order {α : Type*} {d : ℕ} (e₀ : α ≃ Fin d) (x : α → I) (hx : Injective x) :
    ∃ e : α ≃ Fin d, StrictMono (x ∘ e.symm) := by
  let v := x ∘ e₀.symm
  refine ⟨e₀.trans (Tuple.sort v).symm, ?_⟩
  exact (Tuple.monotone_sort v).strictMono_of_injective ((hx.comp e₀.symm.injective).comp (Tuple.sort v).injective)

def legalLabels (p q c n : ℕ) : Set (Element p q c n → I) := {x | Respects x}

lemma legal_ae_rankings (p q c n : ℕ) :
    legalLabels p q c n =ᵐ[cube (Element p q c n)] ⋃ e : Ext p q c n, chamberSlice e.val univ := by
  filter_upwards [cube_injective (Element p q c n)] with x hx
  change Respects x ↔ x ∈ ⋃ e : Ext p q c n, chamberSlice e.val univ
  rw [mem_iUnion]
  constructor
  · intro h
    obtain ⟨e,he⟩ := exists_order (blockOrder p q c n) x hx
    exact ⟨⟨e,(respects_iff_rank x e he).1 h⟩, he, trivial⟩
  · rintro ⟨e,he⟩
    exact (respects_iff_rank x e he.1).2 e.property

lemma extension_probability (p q c n : ℕ) :
    (cube (Element p q c n)).real (legalLabels p q c n) =
      Nat.card (Ext p q c n) * (cube (Fin (Fintype.card (Element p q c n)))).real
        (cone (Fintype.card (Element p q c n))) := by
  classical
  rw [measureReal_congr (legal_ae_rankings p q c n), Nat.card_eq_fintype_card]
  simpa using selected_chambers (fun e : Ext p q c n => e.val) Subtype.val_injective univ MeasurableSet.univ

lemma extension_probability_pos (p q c n : ℕ) : 0 < (cube (Element p q c n)).real (legalLabels p q c n) := by
  rw [extension_probability]
  apply mul_pos (by exact_mod_cast extension_count_pos p q c n)
  have h := cone_mass (Fintype.card (Element p q c n))
  apply lt_of_le_of_ne measureReal_nonneg
  intro eq
  rw [←eq, mul_zero] at h
  norm_num at h

def labelBad {n : ℕ} (p q c : ℕ) (η : ℝ) (z : Fin (n*c+1) → I) : Prop :=
  ∃ i : Fin (n+1), η < |(z (mark c i) : ℝ)-betaQuantile p q c (((i.val:ℝ)+1)/((n:ℝ)+2))|

def meshBad (d : ℕ) (η : ℝ) : Set (Fin d → I) :=
  {v | ∃ j : Fin d, η < |(v j:ℝ)-((j.val:ℝ)+1)/d|}

lemma measurable_meshBad (d : ℕ) (η : ℝ) : MeasurableSet (meshBad d η) := by
  unfold meshBad
  rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  exact measurableSet_lt measurable_const (show Measurable
    (fun v : Fin d → I => |(v j:ℝ)-((j.val:ℝ)+1)/d|) by fun_prop)

lemma sorted_mesh_tail (d : ℕ) (hd : 0 < d) (η : ℝ) (hη : 0 < η) :
    (cube (Fin d)).real {x | x ∘ Tuple.sort x ∈ meshBad d η} ≤ d * (2 * Real.exp (-2*d*η^2)) := by
  apply le_trans (measureReal_mono ?_) (uniform_cube_tail d hd η hη)
  rintro x ⟨j,hj⟩
  refine ⟨j,?_⟩
  let v : Fin d → ℝ := fun i => (x i : ℝ)
  have h : Monotone (v ∘ Tuple.sort x) := fun a b hab =>
    (show (x (Tuple.sort x a) : ℝ) ≤ x (Tuple.sort x b) from Tuple.monotone_sort x hab)
  have e := congrFun (Tuple.comp_sort_eq_comp_iff_monotone.mpr h) j
  change η < |(v ∘ Tuple.sort v) j - ((j.val:ℝ)+1)/d|
  rw [←e]
  exact hj

/-- All marked labels as a single event under the independent labelling of the
original vertices. The denominator conditions on those labels respecting every
window chain. -/
def labelBadFraction (p q c n : ℕ) (η : ℝ) : ℝ :=
  let Q := cube (Element p q c n)
  Q.real (legalLabels p q c n ∩ {x | labelBad p q c η (fun s => x (Sum.inl s))}) /
    Q.real (legalLabels p q c n)

/-- Passing from continuous marked labels to actual extension ranks has an
explicit exponential cost, uniformly over all marks. -/
theorem rank_bound_of_labels (p q c n : ℕ) (η : ℝ) (hη : 0 < η) :
    let d : ℝ := Fintype.card (Element p q c n)
    badFraction p q c n (2*η) ≤ labelBadFraction p q c n η + d*(2*Real.exp (-2*d*η^2)) := by
  classical
  let d := Fintype.card (Element p q c n)
  let Q := cube (Element p q c n)
  let L := legalLabels p q c n
  let B := L ∩ {x | labelBad p q c η (fun s => x (Sum.inl s))}
  let M := ⋃ e : Ext p q c n, chamberSlice e.val (meshBad d η)
  let S := {e : Ranking p q c n // IsExtension e ∧ rankBad (2*η) e}
  let E := ⋃ e : S, chamberSlice e.val univ
  have den : 0 < Q.real L := extension_probability_pos p q c n
  have hc : (cube (Fin d)).real (cone d) ≠ 0 := by
    intro zero
    have eqn := cone_mass d
    rw [zero,mul_zero] at eqn
    norm_num at eqn
  have heq : badFraction p q c n (2*η) = Q.real E / Q.real L := by
    have hm := selected_chambers (fun e : S => e.val) Subtype.val_injective univ MeasurableSet.univ
    simp only [inter_univ] at hm
    change badFraction p q c n (2*η) = _ / (cube (Element p q c n)).real (legalLabels p q c n)
    rw [show Q.real E = Fintype.card S * (cube (Fin d)).real (cone d) from hm, extension_probability]
    change (Nat.card S : ℝ)/Nat.card (Ext p q c n) = _
    rw [Nat.card_eq_fintype_card (α := S)]
    exact (mul_div_mul_right _ _ hc).symm
  have inc : E ⊆ B ∪ M := by
    intro x hx
    obtain ⟨e,he⟩ := mem_iUnion.mp hx
    have actual : x ∈ L := (respects_iff_rank x e.val he.1).2 e.property.1
    by_cases hl : labelBad p q c η (fun s => x (Sum.inl s))
    · exact Or.inl ⟨actual,hl⟩
    · right
      obtain ⟨i,hi⟩ := e.property.2
      let v : Element p q c n := Sum.inl (mark c i)
      let j := e.val v
      apply mem_iUnion.mpr
      refine ⟨⟨e.val,e.property.1⟩, he.1, j, ?_⟩
      have hlabel : |(x v : ℝ) - betaQuantile p q c (((i.val:ℝ)+1)/((n:ℝ)+2))| ≤ η :=
        le_of_not_gt (fun h => hl ⟨i,h⟩)
      let r : ℝ := ((j.val:ℝ)+1)/d
      change 2*η < |r-betaQuantile p q c (((i.val:ℝ)+1)/((n:ℝ)+2))| at hi
      have tri := abs_sub_le r (x v : ℝ) (betaQuantile p q c (((i.val:ℝ)+1)/((n:ℝ)+2)))
      have w : η < |(x v:ℝ)-r| := by rw [abs_sub_comm]; linarith
      simpa [Function.comp_apply, j] using w
  have hd : 0 < d := by dsimp [d]; rw [element_card]; omega
  have : Nonempty (Ext p q c n) := ⟨⟨blockOrder p q c n,isExtension_blockOrder p q c n⟩⟩
  have hm : Q.real M / Q.real L ≤ (d:ℝ)*(2*Real.exp (-2*d*η^2)) := by
    have H := sorted_law_given_rankings (fun e : Ext p q c n => e.val) Subtype.val_injective
      (meshBad d η) (measurable_meshBad d η)
    rw [show Q.real L = Q.real (⋃ e : Ext p q c n, chamberSlice e.val univ) from
      measureReal_congr (legal_ae_rankings p q c n)]
    exact H.le.trans (sorted_mesh_tail d hd η hη)
  rw [heq]
  change Q.real E / Q.real L ≤ Q.real B / Q.real L + _
  calc
    _ ≤ (Q.real B + Q.real M)/Q.real L :=
      div_le_div_of_nonneg_right ((measureReal_mono inc).trans (measureReal_union_le B M)) den.le
    _ ≤ _ := by rw [add_div]; linarith

end
end LeeSah
