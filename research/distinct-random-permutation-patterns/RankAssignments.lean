import Moments
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

namespace DistinctPermutationPatterns
open Finset Filter
open scoped Topology
noncomputable section

/-- Number of full permutations extending k prescribed distinct input/output assignments.
This is the weight of a plot configuration in a factorial-moment calculation. -/
theorem prescribed_assignment_count {n k : ℕ} (a b : Fin k ↪ Fin n) :
    (univ.filter (fun π : Equiv.Perm (Fin n) => ∀ j, π (a j)=b j)).card = (n-k).factorial := by
  classical
  let s : Set (Fin n) := Set.range a
  let t : Set (Fin n) := Set.range b
  let ea : Fin k ≃ s := Equiv.ofInjective a a.injective
  let eb : Fin k ≃ t := Equiv.ofInjective b b.injective
  let eqv : s ≃ t := ea.symm.trans eb
  have hs : Fintype.card s=k := (Fintype.card_congr ea).symm.trans (Fintype.card_fin _)
  have ht : Fintype.card t=k := (Fintype.card_congr eb).symm.trans (Fintype.card_fin _)
  have hsc : Fintype.card (sᶜ : Set (Fin n))=n-k := by
    change Fintype.card {x : Fin n // ¬ x∈s}=n-k
    rw [Fintype.card_subtype_compl,Fintype.card_fin,hs]
  have htc : Fintype.card (tᶜ : Set (Fin n))=n-k := by
    change Fintype.card {x : Fin n // ¬ x∈t}=n-k
    rw [Fintype.card_subtype_compl,Fintype.card_fin,ht]
  let extn := fun π : Equiv.Perm (Fin n) => ∀ x : s, π x=(eqv x : Fin n)
  have eaval (j : Fin k) : (ea j : Fin n)=a j := rfl
  have ebval (j : Fin k) : (eb j : Fin n)=b j := rfl
  have equivalent (π : Equiv.Perm (Fin n)) :
      (∀ j, π (a j)=b j) ↔ extn π := by
    constructor
    · intro h x
      obtain ⟨j,rfl⟩ := ea.surjective x
      simpa only [eqv,Equiv.trans_apply,Equiv.symm_apply_apply,eaval,ebval] using h j
    · intro h j
      simpa only [eqv,Equiv.trans_apply,Equiv.symm_apply_apply,eaval,ebval] using h (ea j)
  let equivFiber : {π : Equiv.Perm (Fin n) // ∀ j, π (a j)=b j} ≃
      {π : Equiv.Perm (Fin n) // extn π} :=
    by
      apply Equiv.subtypeEquiv (Equiv.refl _)
      intro u
      exact equivalent u
  calc
    _ = Fintype.card {π : Equiv.Perm (Fin n) // ∀ j, π (a j)=b j} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card {π : Equiv.Perm (Fin n) // extn π} := Fintype.card_congr equivFiber
    _ = Fintype.card ((sᶜ : Set (Fin n)) ≃ (tᶜ : Set (Fin n))) :=
      Fintype.card_congr (Equiv.Set.compl eqv)
    _ = _ := by rw [Fintype.card_equiv (Fintype.equivOfCardEq (hsc.trans htc.symm)),hsc]

/-- Summing any statistic of k marked values in a uniform permutation weights each injection
by the number of ways to fill the unused positions. -/
theorem sum_on_marked_values {n k : ℕ} (a : Fin k ↪ Fin n) (g : (Fin k ↪ Fin n) → ℕ) :
    (∑ π : Equiv.Perm (Fin n), g (a.trans π.toEmbedding)) = (n-k).factorial * ∑ b, g b := by
  classical
  let f := fun π : Equiv.Perm (Fin n) => a.trans π.toEmbedding
  have c (b : Fin k ↪ Fin n) : (univ.filter (fun π : Equiv.Perm (Fin n) => f π=b)).card =
      (n-k).factorial := by
    convert prescribed_assignment_count a b using 2
    ext π
    simp only [mem_filter,mem_univ,true_and]
    exact ⟨fun eq j => congrArg (fun e : Fin k ↪ Fin n => e j) eq,fun h => Function.Embedding.ext h⟩
  have splitting := sum_fiberwise_of_maps_to' (s:=(univ : Finset (Equiv.Perm (Fin n))))
    (t:=(univ : Finset (Fin k ↪ Fin n))) (g:=f) (fun _ _ => mem_univ _) g
  calc
    _ = ∑ b, ∑ _π ∈ univ.filter (fun π : Equiv.Perm (Fin n) => f π=b), g b := splitting.symm
    _ = _ := by simp only [sum_const,c,nsmul_eq_mul,Nat.cast_id,mul_sum]

private def gapPair {n : ℕ} (d : ℕ) (hd : 0<d) (x : Fin (n-d)) : Fin 2 ↪ Fin n where
  toFun := ![⟨x,by omega⟩,⟨(x:ℕ)+d,by omega⟩]
  inj' := by
    intro i j eq
    fin_cases i <;> fin_cases j <;> simp [Fin.ext_iff] at eq ⊢ <;> omega

/-- Horizontally oriented labelled pairs with exact separation d. -/
def risingPairs (n d : ℕ) : Finset (Fin 2 ↪ Fin n) :=
  univ.filter (fun a : Fin 2 ↪ Fin n => (a 0).val+d=(a 1).val)

theorem card_risingPairs (n d : ℕ) (hd : 0<d) : (risingPairs n d).card = n-d := by
  classical
  rw [← Fintype.card_fin (n-d),←card_univ]
  symm
  apply card_bij (fun x _ => gapPair d hd x)
  · intro x _
    exact mem_filter.mpr ⟨mem_univ _,rfl⟩
  · intro x _ y _ eq
    exact Fin.ext (congrArg (fun p : Fin 2 ↪ Fin n => (p 0).val) eq)
  · intro a ha
    have h : (a 0).val+d=(a 1).val := (mem_filter.mp ha).2
    let x : Fin (n-d) := ⟨(a 0).val,by have := (a 1).isLt; omega⟩
    refine ⟨x,mem_univ _,?_⟩
    ext j
    fin_cases j
    · rfl
    · exact h

/-- For positive horizontal and vertical displacements, count plot pairs rising in both
coordinates. Summing over every permutation gives the exact finite factorial-moment weight. -/
def upPairCount {n : ℕ} (π : Equiv.Perm (Fin n)) (d e : ℕ) : ℕ :=
  ((risingPairs n d).filter (fun a => a.trans π.toEmbedding ∈ risingPairs n e)).card

theorem total_upPairCount (n d e : ℕ) (hd : 0<d) (he : 0<e) :
    (∑ π : Equiv.Perm (Fin n), upPairCount π d e) = (n-d)*(n-e)*(n-2).factorial := by
  classical
  unfold upPairCount
  simp only [card_filter]
  rw [sum_comm]
  have total (a : Fin 2 ↪ Fin n) :
      (∑ π : Equiv.Perm (Fin n), if a.trans π.toEmbedding∈risingPairs n e then 1 else 0) =
      (n-2).factorial*(n-e) := by
    have z := sum_on_marked_values a (fun b => if b∈risingPairs n e then 1 else 0)
    simpa only [←card_filter,filter_mem_eq_inter,univ_inter,card_risingPairs n e he] using z
  simp only [total,sum_const,card_risingPairs n d hd,nsmul_eq_mul,Nat.cast_id]
  ring

/-- Reflection in the value axis counts the downward pairs with the same two distances. -/
def displacementCount {n : ℕ} (π : Equiv.Perm (Fin n)) (d e : ℕ) : ℕ :=
  upPairCount π d e + upPairCount (π.trans Fin.revPerm) d e

private theorem reflected_gap_iff {n : ℕ} (π : Equiv.Perm (Fin n)) (a : Fin 2 ↪ Fin n) (e : ℕ) :
    a.trans (π.trans Fin.revPerm).toEmbedding ∈ risingPairs n e ↔
      (π (a 1)).val+e=(π (a 0)).val := by
  simp only [risingPairs,mem_filter,mem_univ,true_and,Function.Embedding.trans_apply,
    Equiv.coe_toEmbedding,Equiv.trans_apply,Fin.revPerm_apply,Fin.val_rev]
  have h0 := (π (a 0)).isLt
  have h1 := (π (a 1)).isLt
  omega

/-- The two slopes together count the original unordered plot pairs, once each. -/
theorem displacementCount_eq_plot {n : ℕ} (π : Equiv.Perm (Fin n)) (d e : ℕ) (he : 0<e) :
    displacementCount π d e =
      ((risingPairs n d).filter (fun a => (π (a 0)).val+e=(π (a 1)).val ∨
        (π (a 1)).val+e=(π (a 0)).val)).card := by
  classical
  let pos := fun a : Fin 2 ↪ Fin n => (π (a 0)).val+e=(π (a 1)).val
  let neg := fun a : Fin 2 ↪ Fin n => (π (a 1)).val+e=(π (a 0)).val
  have up : upPairCount π d e = ((risingPairs n d).filter pos).card := by
    unfold upPairCount
    apply congrArg card
    exact filter_congr (fun _ _ => by simp [pos,risingPairs])
  have down : upPairCount (π.trans Fin.revPerm) d e = ((risingPairs n d).filter neg).card := by
    unfold upPairCount
    apply congrArg card
    exact filter_congr (fun a _ => reflected_gap_iff π a e)
  have dis : Disjoint ((risingPairs n d).filter pos) ((risingPairs n d).filter neg) := by
    apply disjoint_left.mpr
    intro a ha hb
    have h1 := (mem_filter.mp ha).2
    have h2 := (mem_filter.mp hb).2
    dsimp [pos,neg] at h1 h2
    omega
  rw [displacementCount,up,down,←card_union_of_disjoint dis,←filter_or]

theorem total_displacementCount (n d e : ℕ) (hd : 0<d) (he : 0<e) :
    (∑ π : Equiv.Perm (Fin n), displacementCount π d e) = 2*((n-d)*(n-e)*(n-2).factorial) := by
  classical
  let flip : Equiv.Perm (Equiv.Perm (Fin n)) := (Equiv.refl _).equivCongr Fin.revPerm
  have reindex : (∑ π : Equiv.Perm (Fin n), upPairCount (π.trans Fin.revPerm) d e) =
      ∑ π : Equiv.Perm (Fin n), upPairCount π d e :=
    Fintype.sum_equiv flip _ _ (fun _ => rfl)
  simp only [displacementCount,sum_add_distrib,reindex,total_upPairCount n d e hd he,two_mul]

/-- Exact expectation of the number of unordered plot pairs with two specified positive gaps. -/
theorem mean_displacementCount (n d e : ℕ) (hn : 2≤n) (hd : 0<d) (he : 0<e) :
    uniformAverage (fun π : Equiv.Perm (Fin n) => (displacementCount π d e : ℝ)) =
      2*(↑(n-d):ℝ)*↑(n-e) / ((n:ℝ)*↑(n-1)) := by
  have fac : n.factorial = n*(n-1)*(n-2).factorial := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le' hn
    simp [Nat.factorial_succ,mul_assoc]
  rw [uniformAverage,←Nat.cast_sum,total_displacementCount n d e hd he,
    Fintype.card_perm,Fintype.card_fin,fac]
  push_cast
  have hz : (((n-2).factorial:ℕ):ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp [hz]

/-- For fixed positive horizontal and vertical gaps, the two possible slopes together have
limiting expected count two in the original plot coordinates. -/
theorem mean_displacement_tendsto_two (d e : ℕ) (hd : 0<d) (he : 0<e) :
    Tendsto (fun n => uniformAverage (fun π : Equiv.Perm (Fin n) => (displacementCount π d e : ℝ)))
      atTop (𝓝 2) := by
  have invlim : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have factor (a : ℝ) : Tendsto (fun n : ℕ => 1-a*(n:ℝ)⁻¹) atTop (𝓝 1) := by
    simpa only [mul_zero,sub_zero] using (tendsto_const_nhds (x:= (1:ℝ))).sub (invlim.const_mul a)
  have h := (((factor d).mul (factor e)).div (factor 1) (by norm_num)).const_mul (2:ℝ)
  apply Filter.Tendsto.congr' _ (by simpa using h)
  filter_upwards [eventually_ge_atTop 2,eventually_ge_atTop d,eventually_ge_atTop e]
    with n hn hnd hne
  rw [mean_displacementCount n d e hn hd he,Nat.cast_sub hnd,Nat.cast_sub hne,
    Nat.cast_sub (show 1≤n by omega),Nat.cast_one]
  have nz : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  have nz1 : (n:ℝ)-1≠0 := by
    have z : (2:ℝ)≤n := by exact_mod_cast hn
    linarith
  field_simp [nz,nz1]

end
end DistinctPermutationPatterns

/-- info: 'DistinctPermutationPatterns.mean_displacement_tendsto_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DistinctPermutationPatterns.mean_displacement_tendsto_two

/-- info: 'DistinctPermutationPatterns.prescribed_assignment_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DistinctPermutationPatterns.prescribed_assignment_count

/-- info: 'DistinctPermutationPatterns.displacementCount_eq_plot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DistinctPermutationPatterns.displacementCount_eq_plot

/-- info: 'DistinctPermutationPatterns.mean_displacementCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DistinctPermutationPatterns.mean_displacementCount
