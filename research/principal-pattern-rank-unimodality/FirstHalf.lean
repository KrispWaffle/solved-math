import RankTransfer
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace PrincipalPatternRanks
open Finset DistinctPermutationPatterns
noncomputable section

/-- Weighted m-subsets of the ambient set U which contain A and are contained in Q. -/
def betweenSum {α : Type*} [DecidableEq α] (U : Finset α) (m : ℕ)
    (w : Finset α → ℚ) (A Q : Finset α) : ℚ :=
  ∑ R ∈ U.powersetCard m, if A⊆R ∧ R⊆Q then w R else 0

private theorem sum_between_covers {α : Type*} [DecidableEq α] (U Q : Finset α) (m : ℕ)
    (w : Finset α → ℚ) :
    (∑ T ∈ Q.powersetCard (m+1), betweenSum U m w ∅ T) =
      ((Q.card-m:ℕ):ℚ)*betweenSum U m w ∅ Q := by
  classical
  unfold betweenSum
  simp only [empty_subset,true_and]
  rw [sum_comm,mul_sum]
  apply sum_congr rfl
  intro R hR
  have size := (mem_powersetCard.mp hR).2
  by_cases sub : R⊆Q
  · rw [ite_eq_left sub,←sum_filter,sum_const,nsmul_eq_mul,
      card_filter_powersetCard_subset R Q (m+1) sub (by omega),size]
    simp
  · rw [ite_eq_right sub,mul_zero]
    apply sum_eq_zero
    intro T hT
    exact ite_eq_right (fun h => sub (h.trans (mem_powersetCard.mp hT).1))

private theorem split_between {α : Type*} [DecidableEq α] (U A Q : Finset α) (m : ℕ)
    (w : Finset α → ℚ) (x : α) :
    betweenSum U m w (insert x A) Q + betweenSum U m w A (Q.erase x) =
      betweenSum U m w A Q := by
  classical
  unfold betweenSum
  rw [←sum_add_distrib]
  apply sum_congr rfl
  intro R _
  have erase : R⊆Q.erase x ↔ R⊆Q ∧ x∉R := by
    constructor
    · intro h
      exact ⟨h.trans (erase_subset _ _),fun hx => notMem_erase _ _ (h hx)⟩
    · intro h y hy
      exact mem_erase.mpr ⟨fun eq => h.2 (eq ▸ hy),h.1 hy⟩
  by_cases hA : A⊆R <;> by_cases hQ : R⊆Q <;> by_cases hx : x∈R <;>
    simp [insert_subset_iff,erase,hA,hQ,hx]

/-- Boolean inclusion from m-subsets to (m+1)-subsets is injective below the middle.
This supplies the incidence step in the Pouzet–Rosenberg first-half theorem. -/
theorem incidence_kernel {α : Type*} [DecidableEq α] (U : Finset α) (m : ℕ)
    (small : 2*m+1≤U.card) (w : Finset α → ℚ)
    (zero : ∀ T∈U.powersetCard (m+1), betweenSum U m w ∅ T=0) :
    ∀ R∈U.powersetCard m, w R=0 := by
  classical
  have base (Q : Finset α) (hQ : Q⊆U) (hm : m<Q.card) : betweenSum U m w ∅ Q=0 := by
    have z : (∑ T ∈ Q.powersetCard (m+1), betweenSum U m w ∅ T)=0 :=
      sum_eq_zero (fun T hT => zero T (mem_powersetCard.mpr
        ⟨(mem_powersetCard.mp hT).1.trans hQ,(mem_powersetCard.mp hT).2⟩))
    rw [sum_between_covers] at z
    have h : ((Q.card-m:ℕ):ℚ)≠0 := by exact_mod_cast (show Q.card-m≠0 by omega)
    exact (mul_eq_zero.mp z).resolve_left h
  have vanish (A : Finset α) (Q : Finset α) (hQ : Q⊆U)
      (bound : m+1+A.card≤Q.card) : betweenSum U m w A Q=0 := by
    induction A using Finset.induction_on generalizing Q with
    | empty => exact base Q hQ (by simpa using bound)
    | @insert x A hx ih =>
      rw [card_insert_of_notMem hx] at bound
      have z1 := ih Q hQ (by omega)
      have er : Q.card-1≤(Q.erase x).card := by
        by_cases h : x∈Q
        · rw [card_erase_of_mem h]
        · simp [erase_eq_of_notMem h]
      have z2 := ih (Q.erase x) ((erase_subset _ _).trans hQ) (by omega)
      linarith [split_between U A Q m w x]
  intro R hR
  have size := (mem_powersetCard.mp hR).2
  have v := vanish R U (Subset.rfl) (by omega)
  have just : betweenSum U m w R U = w R := by
    unfold betweenSum
    rw [sum_eq_single_of_mem R hR]
    · rw [ite_eq_left ⟨Subset.rfl,(mem_powersetCard.mp hR).1⟩]
    · intro S hS ne
      exact ite_eq_right (fun h => ne (eq_of_subset_of_card_le h.1
        (by rw [(mem_powersetCard.mp hS).2,size])).symm)
  rwa [just] at v

private def valueRank {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) (x : Fin n) : ℕ :=
  (S.filter (fun y => π y<π x)).card

private theorem rank_lt_of_lt {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    {x y : Fin n} (hx : x∈S) (hxy : π x<π y) : valueRank π S x<valueRank π S y := by
  apply card_lt_card
  have sub : (S.filter (fun b => π b<π x)) ⊆ S.filter (fun b => π b<π y) :=
    fun _ h => mem_filter.mpr ⟨(mem_filter.mp h).1,lt_trans (mem_filter.mp h).2 hxy⟩
  apply (ssubset_iff_of_subset sub).2
  exact ⟨x,mem_filter.mpr ⟨hx,hxy⟩,fun h => lt_irrefl _ (mem_filter.mp h).2⟩

private theorem rank_inj {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    Set.InjOn (valueRank π S) S := by
  intro x hx y hy eq
  rcases lt_trichotomy (π x) (π y) with lt|eqv|gt
  · exact False.elim ((rank_lt_of_lt π S hx lt).ne eq)
  · exact π.injective eqv
  · exact False.elim ((rank_lt_of_lt π S hy gt).ne eq.symm)

private theorem rank_range {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    S.image (valueRank π S)=range S.card := by
  apply eq_of_subset_of_card_le
  · rintro _ h
    obtain ⟨x,hx,rfl⟩ := mem_image.mp h
    exact mem_range.mpr (card_lt_card (filter_ssubset.mpr ⟨x,hx,lt_irrefl _⟩))
  · rw [card_image_of_injOn (rank_inj π S),card_range]

/-- Remove the unique entry of value r from a standardized rank list. -/
def dropRank (P : List ℕ) (r : ℕ) : List ℕ :=
  (P.filter (fun v => decide (v≠r))).map (fun v => v-(if r<v then 1 else 0))

theorem pattern_erase {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    {x : Fin n} (hx : x∈S) :
    pattern π (S.erase x)=dropRank (pattern π S) (valueRank π S x) := by
  classical
  have sortErase : (S.erase x).sort=S.sort.filter (fun y => decide (y≠x)) := by
    apply (S.erase x).sortedLT_sort.eq_of_mem_iff
    · exact (S.sortedLT_sort.pairwise.filter _).sortedLT
    · intro z
      simp [and_comm]
  have retained :
      S.sort.filter ((fun v => decide (v≠valueRank π S x)) ∘ valueRank π S) =
      S.sort.filter (fun y => decide (y≠x)) := by
    apply List.filter_congr
    intro y hy
    have hys : y∈S := (mem_sort _).mp hy
    have same : valueRank π S y=valueRank π S x ↔ y=x := ⟨rank_inj π S hys hx,congrArg _⟩
    simp [same]
  change (S.erase x).sort.map (valueRank π (S.erase x)) =
    dropRank (S.sort.map (valueRank π S)) (valueRank π S x)
  rw [dropRank,List.filter_map,retained,←sortErase,List.map_map]
  apply List.map_congr_left
  intro y hy
  have hys : y∈S := (mem_erase.mp ((mem_sort _).mp hy)).2
  have order : valueRank π S x<valueRank π S y ↔ π x<π y := by
    constructor
    · intro h
      rcases lt_trichotomy (π x) (π y) with lt|eq|gt
      · exact lt
      · exact False.elim (h.ne (congrArg _ (π.injective eq)))
      · exact False.elim (not_lt_of_gt (rank_lt_of_lt π S hys gt) h)
    · exact rank_lt_of_lt π S hx
  change (Finset.filter (fun b => π b<π y) (S.erase x)).card =
    (S.filter (fun b => π b<π y)).card-(if valueRank π S x<valueRank π S y then 1 else 0)
  rw [filter_erase]
  by_cases h : π x < π y
  · rw [ite_eq_left (order.mpr h),card_erase_of_mem (mem_filter.mpr ⟨hx,h⟩)]
  · have absent : x∉S.filter (fun b => π b<π y) := fun hh => h (mem_filter.mp hh).2
    rw [ite_eq_right (fun v => h (order.mp v)),erase_eq_of_notMem absent,Nat.sub_zero]

private theorem powerset_one_less {α : Type*} [DecidableEq α] (T : Finset α) (m : ℕ)
    (size : T.card=m+1) : T.powersetCard m=T.image T.erase := by
  ext S
  constructor
  · intro hm
    obtain ⟨sub,hs⟩ := mem_powersetCard.mp hm
    have card : (T \ S).card=1 := by rw [card_sdiff_of_subset sub,size,hs]; omega
    obtain ⟨x,hx⟩ := card_eq_one.mp card
    have hxt : x∈T \ S := by simp [hx]
    refine mem_image.mpr ⟨x,(mem_sdiff.mp hxt).1,?_⟩
    rw [←sdiff_singleton_eq_erase,←hx,Finset.sdiff_sdiff_eq_self sub]
  · intro h
    obtain ⟨x,hx,rfl⟩ := mem_image.mp h
    exact mem_powersetCard.mpr ⟨erase_subset _ _,by rw [card_erase_of_mem hx,size]; omega⟩

/-- Summing a function of the standardized m-patterns covered by T depends only on T's
standardized list, with multiplicities given by deletions of its possible ranks. -/
theorem sum_pattern_deletions {n m : ℕ} (π : Equiv.Perm (Fin n)) (T : Finset (Fin n))
    (size : T.card=m+1) (g : List ℕ → ℚ) :
    (∑ S ∈ T.powersetCard m, g (pattern π S)) =
      ∑ r ∈ range (m+1), g (dropRank (pattern π T) r) := by
  rw [powerset_one_less T m size,sum_image T.erase_injOn,←size,←rank_range π T,
    sum_image (rank_inj π T)]
  apply sum_congr rfl
  intro x hx
  rw [pattern_erase π T hx]

private def patternsAt {n : ℕ} (π : Equiv.Perm (Fin n)) (m : ℕ) : Finset (List ℕ) :=
  ((univ : Finset (Fin n)).powersetCard m).image (pattern π)

private def extendByZero {E : Finset (List ℕ)} (f : E → ℚ) (P : List ℕ) : ℚ :=
  if h : P∈E then f ⟨P,h⟩ else 0

private def deletionMap {n : ℕ} (π : Equiv.Perm (Fin n)) (m : ℕ) :
    (patternsAt π m → ℚ) →ₗ[ℚ] (patternsAt π (m+1) → ℚ) where
  toFun f Q := ∑ r ∈ range (m+1), extendByZero f (dropRank Q.val r)
  map_add' f g := by
    funext Q
    simp only [Pi.add_apply,←sum_add_distrib]
    apply sum_congr rfl
    intro r _
    by_cases hy : dropRank Q.val r ∈ patternsAt π m <;> simp [extendByZero,hy]
  map_smul' a f := by
    funext Q
    simp only [RingHom.id_apply,Pi.smul_apply,smul_eq_mul,mul_sum]
    apply sum_congr rfl
    intro r _
    by_cases hy : dropRank Q.val r ∈ patternsAt π m <;> simp [extendByZero,hy]

/-- The known increasing-half theorem, on the actual finite downset of each permutation.
Its only rank condition is 2m+1 ≤ n, including the middle pair for odd n. -/
theorem source_first_half {n m : ℕ} (π : Equiv.Perm (Fin n)) (hm : 2*m+1≤n) :
    fixedSizeCount π m ≤ fixedSizeCount π (m+1) := by
  classical
  let U : Finset (Fin n) := univ
  have small : 2*m+1≤U.card := by simpa [U] using hm
  have inj : Function.Injective (deletionMap π m) := by
    intro f g equ
    let w := fun S : Finset (Fin n) =>
      extendByZero f (pattern π S)-extendByZero g (pattern π S)
    have zero (T : Finset (Fin n)) (hT : T∈U.powersetCard (m+1)) : betweenSum U m w ∅ T=0 := by
      have ht := (mem_powersetCard.mp hT).2
      have cut : (U.powersetCard m).filter (fun R => R⊆T)=T.powersetCard m := by
        ext R
        simp [U,and_comm]
      have hP : pattern π T ∈ patternsAt π (m+1) := mem_image_of_mem _ hT
      have e := congrFun equ (⟨pattern π T,hP⟩ : patternsAt π (m+1))
      unfold betweenSum
      simp only [empty_subset,true_and,←sum_filter,cut,w,sum_sub_distrib,
        sum_pattern_deletions π T ht]
      exact sub_eq_zero.mpr e
    have kernel := incidence_kernel U m small w zero
    funext P
    obtain ⟨S,hS,e⟩ := mem_image.mp P.property
    have eqv := kernel S hS
    change extendByZero f (pattern π S)-extendByZero g (pattern π S)=0 at eqv
    rw [e] at eqv
    simpa [extendByZero,P.property] using sub_eq_zero.mp eqv
  have inequality := LinearMap.finrank_le_finrank_of_injective inj
  calc
    fixedSizeCount π m = Fintype.card (patternsAt π m) := (Fintype.card_coe _).symm
    _ = Module.finrank ℚ (patternsAt π m → ℚ) :=
      (Module.finrank_fintype_fun_eq_card ℚ (η:=↥(patternsAt π m))).symm
    _ ≤ Module.finrank ℚ (patternsAt π (m+1) → ℚ) := inequality
    _ = Fintype.card (patternsAt π (m+1)) :=
      Module.finrank_fintype_fun_eq_card ℚ (η:=↥(patternsAt π (m+1)))
    _ = fixedSizeCount π (m+1) := Fintype.card_coe _

/-- Only normalized upper-rank curvature remains as a hypothesis to obtain the
source's unimodality property for an individual host. -/
theorem source_unimodal_of_upper_curvature {n k : ℕ} (π : Equiv.Perm (Fin n)) (hk : 2*k≤n+1)
    (curvature : ∀ j, k≤j → j+2≤n → normalizedRank π j * normalizedRank π (j+2) <
      (1+4/(n:ℝ))*(normalizedRank π (j+1))^2) : RankUnimodal π :=
  source_unimodal_of_curvature π (fun i hi => source_first_half π (by omega)) curvature

end
end PrincipalPatternRanks

/-- info: 'PrincipalPatternRanks.source_first_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrincipalPatternRanks.source_first_half

/-- info: 'PrincipalPatternRanks.source_unimodal_of_upper_curvature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrincipalPatternRanks.source_unimodal_of_upper_curvature
