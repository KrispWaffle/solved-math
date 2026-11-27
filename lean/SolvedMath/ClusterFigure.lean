module

public import SolvedMath.ClusterLimit
import Mathlib.Tactic.Linarith

/-! Figure 3 uses zero-based ranks divided by the difference of the two endpoint ranks. -/
@[expose] public section
namespace LeeSah
open Filter
open scoped Topology
noncomputable section

def figureBad {p q c n : ℕ} (ε : ℝ) (e : Ranking p q c n) : Prop :=
  ∃ i : Fin (n+1), ε <
    |((e (.inl (mark c i))).val : ℝ) / ((Fintype.card (Element p q c n):ℝ)-1) -
       betaQuantile p q c (((i.val:ℝ)+1)/((n:ℝ)+2))|
def figureBadFraction (p q c n : ℕ) (ε : ℝ) : ℝ :=
  (Nat.card {e : Ranking p q c n // IsExtension e ∧ figureBad ε e} : ℝ) /
    Nat.card {e : Ranking p q c n // IsExtension e}
private theorem figure_tail (p q c : ℕ) (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
      figureBadFraction p q c n ε ≤ C*Real.exp (-κ*(n:ℝ)) := by
  obtain ⟨C,κ,hC,hκ,tail⟩ := extension_rank_tail_all p q c hc (ε/2) (half_pos hε)
  refine ⟨C,κ,hC,hκ,?_⟩
  have fine : ∀ᶠ n : ℕ in atTop, 1/(n:ℝ) < ε/2 :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually_lt_const (half_pos hε)
  filter_upwards [fine, eventually_ge_atTop 1] with n hf hn
  let D := Fintype.card (Element p q c n)
  have hND : n < D := by
    dsimp [D]
    rw [element_card]
    have le := Nat.le_mul_of_pos_left n (show 0 < p+q+c by omega)
    omega
  have hd : (1 : ℝ) < D := by exact_mod_cast (lt_of_le_of_lt hn hND)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have mesh : 1/(D:ℝ) < ε/2 :=
    (one_div_le_one_div_of_le hnR (by exact_mod_cast hND.le)).trans_lt hf
  have inc (e : Ranking p q c n) (bad : figureBad ε e) : rankBad (ε/2) e := by
    obtain ⟨i, hi⟩ := bad
    let v := e (.inl (mark c i))
    let r : ℝ := (v.val:ℝ)+1
    let f := betaQuantile p q c (((i.val:ℝ)+1)/((n:ℝ)+2))
    have hr1 : 1 ≤ r := by dsimp [r]; linarith [Nat.cast_nonneg (α := ℝ) v.val]
    have hrd : r ≤ D := by
      dsimp only [r]
      exact_mod_cast (Nat.succ_le_of_lt v.isLt)
    have norm := rank_conventions hd hr1 hrd
    change ε < |(v.val:ℝ)/((D:ℝ)-1) - f| at hi
    have eq : (v.val:ℝ)/((D:ℝ)-1) = (r-1)/((D:ℝ)-1) := by simp [r]
    rw [eq] at hi
    refine ⟨i,?_⟩
    change ε/2 < |r/(D:ℝ)-f|
    have tri := abs_sub_le ((r-1)/((D:ℝ)-1)) (r/(D:ℝ)) f
    rw [abs_sub_comm ((r-1)/((D:ℝ)-1)) (r/(D:ℝ))] at tri
    linarith
  let S := {e : Ranking p q c n // IsExtension e ∧ figureBad ε e}
  let T := {e : Ranking p q c n // IsExtension e ∧ rankBad (ε/2) e}
  let inj (x : S) : T := ⟨x.val,x.property.1,inc x.val x.property.2⟩
  have hi : Function.Injective inj :=
    fun _ _ h => Subtype.ext (congrArg (fun y : T => y.val) h)
  have hcount : (Nat.card S:ℝ) ≤ Nat.card T := by
    exact_mod_cast Nat.card_le_card_of_injective inj hi
  exact (div_le_div_of_nonneg_right hcount (show 0 ≤ (Nat.card (Ext p q c n):ℝ) by positivity)).trans (tail n)
/-- The plotted zero-based rank convention has the same uniform limit. -/
theorem figure_normalization :
    ∀ m a b : ℕ, 1 ≤ a → a < b → b ≤ m → ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => figureBadFraction (a-1) (m-b) (b-a) n ε) atTop (𝓝 0) := by
  intro m a b _ hab _ ε hε
  obtain ⟨C,κ,_,hκ,h⟩ := figure_tail (a-1) (m-b) (b-a) (Nat.sub_pos_of_lt hab) ε hε
  have conv : Tendsto (fun n : ℕ => Real.exp (-κ*(n:ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hκ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using conv.const_mul C) (Eventually.of_forall fun n => by unfold figureBadFraction; positivity) h

end
end LeeSah
