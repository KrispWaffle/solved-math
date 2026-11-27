import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Polynomial identities and the sign test for the aggregate Jacobi–Stirling
insertion. The all-row Turán inequality remains a research hypothesis. -/

namespace JacobiStirlingRoots
open Polynomial
noncomputable section

def insert (j : ℕ) (f : ℝ[X]) : ℝ[X] :=
  (1 + C (j : ℝ) * X) * f + X * (1+X) * derivative f

def wronskian (f g : ℝ[X]) : ℝ[X] := derivative f*g - f*derivative g

def turan (prev f next : ℝ[X]) : ℝ[X] := f^2-prev*next

theorem insertion_determinant (j : ℕ) (prev f next : ℝ[X]) :
    (insert j f+prev)*next - (insert j next+f)*f =
      X*(1+X)*wronskian f next - turan prev f next := by
  unfold insert wronskian turan
  ring

theorem negative_at_next_root (j : ℕ) (prev f next : ℝ[X]) (x : ℝ)
    (left : -1 < x) (right : x < 0) (root : IsRoot (insert j next+f) x)
    (orientation : 0 < (wronskian f next).eval x)
    (bound : 0 ≤ (turan prev f next).eval x) :
    (insert j f+prev).eval x * next.eval x < 0 := by
  have id := congrArg (fun p : ℝ[X] => p.eval x) (insertion_determinant j prev f next)
  change (insert j next+f).eval x = 0 at root
  simp only [eval_sub, eval_mul, eval_add, eval_X, eval_one] at id root
  rw [root, zero_mul, sub_zero] at id
  rw [eval_add, id]
  have neg : x * (1+x) < 0 := mul_neg_of_neg_of_pos right (by linarith)
  exact sub_neg.mpr (lt_of_lt_of_le (mul_neg_of_neg_of_pos neg orientation) bound)

theorem strip_padding (j : ℕ) (f : ℝ[X]) :
    insert j ((1+X)*f) = (1+X)*insert (j+1) f := by
  simp only [insert, derivative_mul, derivative_one, derivative_X,
    zero_add, one_mul, Nat.cast_add, Nat.cast_one, map_add, map_one]
  ring

end
end JacobiStirlingRoots
