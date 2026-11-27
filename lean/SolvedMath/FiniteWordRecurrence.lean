import Mathlib.Algebra.LinearRecurrence
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace FiniteWordRecurrence

variable {S A : Type*}

def follow (δ : S → A → S) (s : S) (l : List A) : S := l.foldr (fun a v => δ v a) s

theorem follow_snoc (δ : S → A → S) (s : S) (l : List A) (a : A) :
    follow δ s (l++[a]) = follow δ (δ s a) l := by simp [follow,List.foldr_append]

/-- The operator for one letter, with multiplicity if distinct letters give the same successor. -/
def operator [Fintype A] (δ : S → A → S) : Module.End ℚ (S → ℚ) where
  toFun g s := ∑ a, g (δ s a)
  map_add' g h := by ext s; simp [Finset.sum_add_distrib]
  map_smul' c g := by ext s; simp [Finset.mul_sum]

theorem count_eq_orbit [Fintype A] (δ : S → A → S) (g : S → ℚ) (N : ℕ) (s : S) :
    (∑ f : Fin N → A, g (follow δ s (List.ofFn f).reverse)) = ((operator δ)^N) g s := by
  classical
  induction N generalizing s with
  | zero => simp [follow,List.ofFn_zero]
  | succ N ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (N+1) => A)).sum_comp]
    simp_rw [Fintype.sum_prod_type,Fin.consEquiv_apply,List.ofFn_cons,List.reverse_cons,
      follow_snoc,ih]
    rw [pow_succ',mul_apply_eq_comp]
    rfl

/-- One recurrence, obtained from the characteristic polynomial, works for every initial vector
and observed coordinate of a finite transfer operator. -/
theorem orbit_recurrence [Fintype S] (T : Module.End ℚ (S → ℚ)) :
    ∃ E : LinearRecurrence ℚ, ∀ (v : S → ℚ) (s : S), E.IsSolution (fun k => (T^k) v s) := by
  classical
  let P := T.charpoly
  let d := P.natDegree
  refine ⟨⟨d,fun i => -P.coeff i⟩,?_⟩
  intro v s k
  have root : Polynomial.aeval T P = 0 := T.aeval_self_charpoly
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ,
    (show P.Monic from T.charpoly_monic).coeff_natDegree,one_smul] at root
  rw [← Fin.sum_univ_eq_sum_range] at root
  have at_state := congrArg (fun L : Module.End ℚ (S→ℚ) => L ((T^k) v) s) root
  simp only [LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply,Pi.add_apply,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul,LinearMap.zero_apply,Pi.zero_apply] at at_state
  have powers (j : ℕ) : (T^j) ((T^k) v) = (T^(k+j)) v := by
    rw [Nat.add_comm, pow_add,mul_apply_eq_comp]
  simp_rw [powers] at at_state
  change (T^(k+d)) v s = ∑ i : Fin d, (-P.coeff i) * (T^(k+i.val)) v s
  simp only [neg_mul,Finset.sum_neg_distrib]
  apply eq_neg_of_add_eq_zero_left
  rwa [add_comm]

theorem periodic_recurrence [Fintype S] [Fintype A] (δ : S → A → S) (stride : ℕ) :
    ∃ E : LinearRecurrence ℚ, ∀ (g : S→ℚ) (s : S) (offset : ℕ),
      E.IsSolution (fun k => ∑ f : Fin (stride*k+offset) → A,
        g (follow δ s (List.ofFn f).reverse)) := by
  obtain ⟨E,hE⟩ := orbit_recurrence ((operator δ)^stride)
  refine ⟨E,fun g s offset => ?_⟩
  simpa only [count_eq_orbit,pow_add,pow_mul,mul_apply_eq_comp] using
    hE (((operator δ)^offset) g) s

end FiniteWordRecurrence
