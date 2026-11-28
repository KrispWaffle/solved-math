import SolvedMath.RandomPatternDisplacements
import Mathlib.Data.Finset.Prod

namespace PrincipalPatternRanks

open Finset DistinctPermutationPatterns
noncomputable section

/-- Uniform random ordering represented by the image of each successive position. -/
def flagSet {n : ℕ} (π : Equiv.Perm (Fin n)) (m : ℕ) : Finset (Fin n) :=
  (univ.filter (fun i : Fin n => i.val < m)).image π

private theorem prefix_step {n m : ℕ} (π : Equiv.Perm (Fin n)) (hm : m<n) :
    flagSet π (m+1) = insert (π ⟨m,hm⟩) (flagSet π m) := by
  classical
  unfold flagSet
  rw [←image_insert]
  apply congrArg (image π)
  ext j
  simp only [mem_filter,mem_univ,true_and,mem_insert,Fin.ext_iff]
  omega

/-- A function of the marked coordinates only, averaged over the uniform size-m slice. -/
def sliceMean {n : ℕ} (B : Finset (Fin n)) (h : Finset (Fin n) → ℝ) (m : ℕ) : ℝ :=
  uniformAverage (fun π : Equiv.Perm (Fin n) => h (flagSet π m ∩ B))

private def twoLabels {n : ℕ} (i j : Fin n) (hne : i≠j) : Fin 2 ↪ Fin n where
  toFun := ![i,j]
  inj' := by
    intro x y eq
    fin_cases x <;> fin_cases y <;> simp_all

private theorem card_marked_pairs {n : ℕ} (B : Finset (Fin n)) :
    (univ.filter (fun a : Fin 2 ↪ Fin n => a 0∈B ∧ a 1∈B)).card = B.card*B.card-B.card := by
  classical
  rw [←offDiag_card]
  apply card_bij (fun a _ => (a 0,a 1))
  · intro a ha
    exact mem_offDiag.mpr ⟨(mem_filter.mp ha).2.1,(mem_filter.mp ha).2.2,
      a.injective.ne (by decide)⟩
  · intro a _ b _ eq
    apply Function.Embedding.ext
    intro j
    fin_cases j
    · exact congrArg Prod.fst eq
    · exact congrArg Prod.snd eq
  · rintro ⟨x,y⟩ hxy
    obtain ⟨hx,hy,hne⟩ := mem_offDiag.mp hxy
    exact ⟨twoLabels x y hne,mem_filter.mpr ⟨mem_univ _,hx,hy⟩,rfl⟩

/-- Exact number of flags in which the next two distinct positions both carry marked labels. -/
theorem flags_two_marked {n : ℕ} (B : Finset (Fin n)) (i j : Fin n) (hne : i≠j) :
    (∑ π : Equiv.Perm (Fin n), if π i ∈ B ∧ π j ∈ B then 1 else 0) =
      (n-2).factorial*(B.card*B.card-B.card) := by
  classical
  let a := twoLabels i j hne
  have z := sum_on_marked_values a (fun b => if b 0∈B ∧ b 1∈B then 1 else 0)
  change (∑ π : Equiv.Perm (Fin n),
    if (a.trans π.toEmbedding) 0 ∈ B ∧ (a.trans π.toEmbedding) 1 ∈ B then 1 else 0) = _
  rw [z,←card_filter,card_marked_pairs]

private theorem prefix_swap {n m : ℕ} (π : Equiv.Perm (Fin n)) (hm : m+1<n) :
    let i : Fin n := ⟨m,by omega⟩
    let j : Fin n := ⟨m+1,hm⟩
    flagSet ((Equiv.swap i j).trans π) m = flagSet π m := by
  classical
  dsimp only
  unfold flagSet
  apply image_congr
  intro x hx
  have small := (mem_filter.mp hx).2
  have hi : x ≠ (⟨m,by omega⟩ : Fin n) := by
    intro eq
    have e := congrArg Fin.val eq
    dsimp at e
    omega
  have hj : x ≠ (⟨m+1,hm⟩ : Fin n) := by
    intro eq
    have e := congrArg Fin.val eq
    dsimp at e
    omega
  simp [Equiv.swap_apply_of_ne_of_ne hi hj]

private theorem sum_mixed_difference {n m : ℕ} (hm : m+1<n) (H : Finset (Fin n) → ℝ) :
    let i : Fin n := ⟨m,by omega⟩
    let j : Fin n := ⟨m+1,hm⟩
    (∑ π : Equiv.Perm (Fin n), H (flagSet π (m+2))) -
      2*(∑ π : Equiv.Perm (Fin n), H (flagSet π (m+1))) +
      (∑ π : Equiv.Perm (Fin n), H (flagSet π m)) =
      ∑ π : Equiv.Perm (Fin n), (H (insert (π j) (insert (π i) (flagSet π m)))
       - H (insert (π i) (flagSet π m)) - H (insert (π j) (flagSet π m)) + H (flagSet π m)) := by
  classical
  dsimp only
  let i : Fin n := ⟨m,by omega⟩
  let j : Fin n := ⟨m+1,hm⟩
  let swap : Equiv.Perm (Equiv.Perm (Fin n)) := (Equiv.swap i j).equivCongr (Equiv.refl _)
  have eq : (∑ π : Equiv.Perm (Fin n), H (insert (π i) (flagSet π m))) =
      ∑ π : Equiv.Perm (Fin n), H (insert (π j) (flagSet π m)) := by
    apply Fintype.sum_equiv swap
    intro π
    change H (insert (π i) (flagSet π m)) =
      H (insert (π ((Equiv.swap i j).symm j)) (flagSet ((Equiv.swap i j).symm.trans π) m))
    rw [Equiv.symm_swap,Equiv.swap_apply_right,prefix_swap π hm]
  simp only [prefix_step _ hm,prefix_step _ (show m<n by omega),sum_add_distrib,sum_sub_distrib]
  change _ - 2*(∑ π : Equiv.Perm (Fin n), H (insert (π i) (flagSet π m))) + _ = _
  linarith

private theorem mixed_pointwise {n : ℕ} (B S : Finset (Fin n)) (x y : Fin n)
    (h : Finset (Fin n) → ℝ) (bounded : ∀ U, 0≤h U ∧ h U≤1) :
    |h (insert y (insert x S) ∩ B) - h (insert x S ∩ B) -
      h (insert y S ∩ B) + h (S ∩ B)| ≤ if x∈B ∧ y∈B then 2 else 0 := by
  classical
  by_cases hx : x∈B <;> by_cases hy : y∈B
  · simp only [hx,hy,and_self,ite_true]
    exact abs_le.mpr ⟨by linarith [(bounded (insert y (insert x S) ∩ B)).1,
      (bounded (insert x S ∩ B)).2,(bounded (insert y S ∩ B)).2,(bounded (S ∩ B)).1],
      by linarith [(bounded (insert y (insert x S) ∩ B)).2,
      (bounded (insert x S ∩ B)).1,(bounded (insert y S ∩ B)).1,(bounded (S ∩ B)).2]⟩
  all_goals simp [hx,hy,insert_inter_of_mem,insert_inter_of_notMem]

/-- Curvature of the actual slice averages. Only flags placing both newly added
labels in the determining set can contribute to their second difference. -/
theorem slice_second_difference {n m : ℕ} (hm : m+1<n) (B : Finset (Fin n))
    (h : Finset (Fin n) → ℝ) (bounded : ∀ U, 0≤h U ∧ h U≤1) :
    |sliceMean B h (m+2)-2*sliceMean B h (m+1)+sliceMean B h m| ≤
      2*(B.card:ℝ)*((B.card:ℝ)-1)/((n:ℝ)*((n:ℝ)-1)) := by
  classical
  let i : Fin n := ⟨m,by omega⟩
  let j : Fin n := ⟨m+1,hm⟩
  have hne : i≠j := by
    intro eq
    have e := congrArg Fin.val eq
    change m=m+1 at e
    omega
  let H := fun S : Finset (Fin n) => h (S ∩ B)
  let diff := fun π : Equiv.Perm (Fin n) =>
    H (insert (π j) (insert (π i) (flagSet π m))) - H (insert (π i) (flagSet π m))
      -H (insert (π j) (flagSet π m))+H (flagSet π m)
  let N : ℝ := Fintype.card (Equiv.Perm (Fin n))
  have hN : 0≤N := by dsimp [N]; positivity
  have avg : sliceMean B h (m+2)-2*sliceMean B h (m+1)+sliceMean B h m =
      (∑ π, diff π)/N := by
    change (∑ π, H (flagSet π (m+2)))/N-2*((∑ π, H (flagSet π (m+1)))/N)+
      (∑ π, H (flagSet π m))/N = _
    rw [←sum_mixed_difference hm H]
    ring
  have hsum : (∑ π, |diff π|) ≤
      2*(↑((n-2).factorial*(B.card*B.card-B.card)):ℝ) := by
    calc
      (∑ π, |diff π|) ≤ ∑ π : Equiv.Perm (Fin n), (2:ℝ)*((if π i∈B ∧ π j∈B then 1 else 0 : ℕ) : ℝ) := by
        apply sum_le_sum
        intro π _
        have r := mixed_pointwise B (flagSet π m) (π i) (π j) h bounded
        by_cases hh : π i∈B ∧ π j∈B <;> simpa [diff,H,hh] using r
      _ = _ := by rw [←mul_sum,←Nat.cast_sum,flags_two_marked B i j hne]
  rw [avg,abs_div,abs_of_nonneg hN]
  calc
    _ ≤ (2*↑((n-2).factorial*(B.card*B.card-B.card)))/N :=
      div_le_div_of_nonneg_right ((abs_sum_le_sum_abs _ _).trans hsum) hN
    _ = _ := by
      have cardle : B.card≤B.card*B.card := Nat.le_mul_self B.card
      have fac : n.factorial = n*(n-1)*(n-2).factorial := by
        obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le' (show 2≤n by omega)
        simp [Nat.factorial_succ,mul_assoc]
      dsimp [N]
      rw [Fintype.card_perm,Fintype.card_fin,fac]
      push_cast [Nat.cast_sub cardle,Nat.cast_sub (show 1≤n by omega)]
      have hz : (((n-2).factorial:ℕ):ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hn : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
      have h1 : (n:ℝ)-1≠0 := by
        have r : (2:ℝ)≤n := by exact_mod_cast (show 2≤n by omega)
        linarith
      field_simp

end
end PrincipalPatternRanks

/-- info: 'PrincipalPatternRanks.slice_second_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PrincipalPatternRanks.slice_second_difference
