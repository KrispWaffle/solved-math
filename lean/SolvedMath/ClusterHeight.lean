module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Basic
public import SolvedMath.ClusterOrderStatistics
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Source statement of Lee and Sah's Conjecture 6.1. An extension is a
bijection with the ranks that respects every spine and branch chain. -/
@[expose] public section
namespace LeeSah
open Filter MeasureTheory Set
open scoped Topology Interval
noncomputable section

abbrev Element (p q c n : ℕ) :=
  Fin (n*c+1) ⊕ ((Fin n × Fin p) ⊕ (Fin n × Fin q))

def mark {n : ℕ} (c : ℕ) (i : Fin (n+1)) : Fin (n*c+1) :=
  ⟨i.val*c, Nat.lt_succ_of_le (Nat.mul_le_mul_right c (by omega))⟩

abbrev Ranking (p q c n : ℕ) := Element p q c n ≃ Fin (Fintype.card (Element p q c n))

def Respects {p q c n : ℕ} {β : Type*} [Preorder β] (e : Element p q c n → β) : Prop :=
  StrictMono (fun s => e (Sum.inl s)) ∧
  (∀ w : Fin n, StrictMono (fun j : Fin p => e (Sum.inr (Sum.inl (w,j))))) ∧
  (∀ w : Fin n, StrictMono (fun j : Fin q => e (Sum.inr (Sum.inr (w,j))))) ∧
  (∀ (w : Fin n) (j : Fin p), e (Sum.inr (Sum.inl (w,j))) < e (Sum.inl (mark c w.castSucc))) ∧
  (∀ (w : Fin n) (j : Fin q), e (Sum.inl (mark c w.succ)) < e (Sum.inr (Sum.inr (w,j))))

def IsExtension {p q c n : ℕ} (e : Ranking p q c n) : Prop := Respects (p := p) (q := q) (c := c) (n := n) e

def betaWeight (p q c : ℕ) (x : ℝ) : ℝ :=
  x ^ ((p:ℝ)/c) * (1-x) ^ ((q:ℝ)/c)

def betaCdf (p q c : ℕ) (x : ℝ) : ℝ :=
  (∫ t in (0:ℝ)..x, betaWeight p q c t) / (∫ t in (0:ℝ)..1, betaWeight p q c t)

def betaQuantile (p q c : ℕ) (u : ℝ) : ℝ :=
  sInf {x : ℝ | x ∈ Icc 0 1 ∧ u ≤ betaCdf p q c x}

def rankBad {p q c n : ℕ} (ε : ℝ) (e : Ranking p q c n) : Prop :=
  ∃ i : Fin (n+1),
    ε < |(((e (Sum.inl (mark c i))).val + 1 : ℝ) / Fintype.card (Element p q c n)) -
       betaQuantile p q c (((i.val:ℝ)+1)/((n:ℝ)+2))|

def badFraction (p q c n : ℕ) (ε : ℝ) : ℝ :=
  (Nat.card {e : Ranking p q c n // IsExtension e ∧ rankBad ε e} : ℝ) /
    Nat.card {e : Ranking p q c n // IsExtension e}

/-- Conjecture 6.1 with one-based normalized ranks, simultaneous in every marked point. -/
def Conjecture61 : Prop :=
  ∀ (m a b : ℕ), 1 ≤ a → a < b → b ≤ m → ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => badFraction (a-1) (m-b) (b-a) n ε) atTop (𝓝 0)

theorem element_card (p q c n : ℕ) : Fintype.card (Element p q c n) = (p+q+c)*n+1 := by
  simp only [Element, Fintype.card_sum, Fintype.card_fin, Fintype.card_prod]
  ring

/-- An explicit legal extension that puts the lower branches before the spine and the upper branches after it. -/
def blockOrder (p q c n : ℕ) : Ranking p q c n :=
  let reorder := ((Equiv.sumAssoc (Fin (n*c+1)) (Fin n × Fin p) (Fin n × Fin q)).symm.trans
    (Equiv.sumCongr (Equiv.sumComm _ _) (Equiv.refl _))).trans (Equiv.sumAssoc _ _ _)
  let after := (Equiv.sumCongr (Equiv.refl (Fin (n*c+1))) (@finProdFinEquiv n q)).trans finSumFinEquiv
  (reorder.trans ((Equiv.sumCongr (@finProdFinEquiv n p) after).trans finSumFinEquiv)).trans
    (finCongr (by rw [element_card]; ring))

lemma isExtension_blockOrder (p q c n : ℕ) : IsExtension (blockOrder p q c n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    change n*p+i.val < n*p+j.val
    omega
  · intro w i j hij
    change i.val+p*w.val < j.val+p*w.val
    omega
  · intro w i j hij
    change n*p+(n*c+1+(i.val+q*w.val)) < n*p+(n*c+1+(j.val+q*w.val))
    omega
  · intro w j
    have h := (finProdFinEquiv (w,j)).isLt
    change j.val+p*w.val < n*p at h
    change j.val+p*w.val < n*p+_
    omega
  · intro w j
    have h := (mark c w.succ).isLt
    change n*p+(mark c w.succ).val < n*p+(n*c+1+(j.val+q*w.val))
    omega

lemma extension_count_pos (p q c n : ℕ) : 0 < Nat.card {e : Ranking p q c n // IsExtension e} := by
  have : Nonempty {e : Ranking p q c n // IsExtension e} :=
    ⟨⟨blockOrder p q c n, isExtension_blockOrder p q c n⟩⟩
  exact Nat.card_pos

theorem badFraction_nonneg (p q c n : ℕ) (ε : ℝ) : 0 ≤ badFraction p q c n ε := by
  unfold badFraction
  positivity

/-- The product of c factors with exponent p/c restores the integral power p. -/
private theorem fractional_power (x : ℝ) (p c : ℕ) (hx : 0 ≤ x) (hc : 0 < c) :
    (x ^ ((p:ℝ) / c)) ^ c = x ^ p := by
  rw [← Real.rpow_mul_natCast hx, div_mul_cancel₀ _ (by exact_mod_cast hc.ne'), Real.rpow_natCast]

/-- Between the endpoints of a single window the beta-density product has two
explicit endpoint bounds, including zero lower or upper branch lengths. -/
theorem block_bounds (p q c : ℕ) (hc : 0 < c) (u v : ℝ) (hu : 0 ≤ u) (hv : v ≤ 1)
    (t : ℕ → ℝ) (inside : ∀ j < c, u ≤ t j ∧ t j ≤ v) :
    u^p * (1-v)^q ≤ ∏ j ∈ Finset.range c, betaWeight p q c (t j) ∧
    (∏ j ∈ Finset.range c, betaWeight p q c (t j)) ≤ v^p * (1-u)^q := by
  have huv := le_trans (inside 0 hc).1 (inside 0 hc).2
  have hpow (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      (x ^ ((p:ℝ)/c) * y ^ ((q:ℝ)/c)) ^ c = x^p*y^q := by
    rw [mul_pow, fractional_power x p c hx hc, fractional_power y q c hy hc]
  have ex : 0 ≤ (p:ℝ)/c := by positivity
  have ey : 0 ≤ (q:ℝ)/c := by positivity
  constructor
  · rw [← hpow u (1-v) hu (by linarith)]
    calc
      _ = ∏ _ ∈ Finset.range c, u ^ ((p:ℝ)/c) * (1-v) ^ ((q:ℝ)/c) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => mul_nonneg (Real.rpow_nonneg hu _)
        (Real.rpow_nonneg (by linarith) _)) (fun j hj => by
          obtain ⟨h1, h2⟩ := inside j (Finset.mem_range.mp hj)
          exact mul_le_mul (Real.rpow_le_rpow hu h1 ex)
            (Real.rpow_le_rpow (by linarith) (by linarith) ey)
            (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _))
  · rw [← hpow v (1-u) (by linarith) (by linarith)]
    calc
      _ ≤ ∏ _ ∈ Finset.range c, v ^ ((p:ℝ)/c) * (1-u) ^ ((q:ℝ)/c) :=
        Finset.prod_le_prod₀ (fun j hj => by
          obtain ⟨h1, h2⟩ := inside j (Finset.mem_range.mp hj)
          exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _))
          (fun j hj => by
            obtain ⟨h1, h2⟩ := inside j (Finset.mem_range.mp hj)
            exact mul_le_mul (Real.rpow_le_rpow (by linarith) h2 ex)
              (Real.rpow_le_rpow (by linarith) (by linarith) ey)
              (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _))
      _ = _ := by simp

def spineWeight (p q c : ℕ) (z : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, z (i*c)^p * (1-z ((i+1)*c))^q

def sampleWeight (p q c : ℕ) (z : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range c, betaWeight p q c (z (i*c+j+1))

/-- The global telescope in the proof, written without denominators so that it
also applies to boundary coordinates. A finite ordered spine can be extended
constantly past its last index. -/
theorem density_sandwich (p q c : ℕ) (hc : 0 < c) (z : ℕ → ℝ)
    (sorted : Monotone z) (unit : ∀ k, z k ∈ Icc 0 1) (n : ℕ) :
    spineWeight p q c z n ≤ sampleWeight p q c z n ∧
    z 0^p * (1-z (n*c))^q * sampleWeight p q c z n ≤
      z (n*c)^p * (1-z 0)^q * spineWeight p q c z n := by
  have sampleNonneg (k : ℕ) : 0 ≤ sampleWeight p q c z k := by
    exact Finset.prod_nonneg (fun i _ => Finset.prod_nonneg (fun j _ =>
      mul_nonneg (Real.rpow_nonneg (unit _).1 _)
        (Real.rpow_nonneg (sub_nonneg.mpr (unit _).2) _)))
  induction n with
  | zero => simp [spineWeight, sampleWeight]
  | succ n ih =>
    have bounds := block_bounds p q c hc (z (n*c)) (z ((n+1)*c)) (unit _).1 (unit _).2
      (fun j => z (n*c+j+1)) (fun j hj => ⟨sorted (by omega), sorted (by rw [Nat.add_mul]; omega)⟩)
    have nonneg (i : ℕ) : 0 ≤ (1-z i)^q := pow_nonneg (sub_nonneg.mpr (unit _).2) _
    simp only [spineWeight, sampleWeight, Finset.prod_range_succ] at ih ⊢
    constructor
    · exact mul_le_mul ih.1 bounds.1 (mul_nonneg (pow_nonneg (unit _).1 _) (nonneg _)) (sampleNonneg n)
    · calc
        _ ≤ z 0^p * (1-z ((n+1)*c))^q *
              (sampleWeight p q c z n * (z ((n+1)*c)^p * (1-z (n*c))^q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left bounds.2 (sampleNonneg n))
            (mul_nonneg (pow_nonneg (unit _).1 _) (nonneg _))
        _ = (z 0^p * (1-z (n*c))^q * sampleWeight p q c z n) *
              (z ((n+1)*c)^p * (1-z ((n+1)*c))^q) := by ring
        _ ≤ (z (n*c)^p * (1-z 0)^q * spineWeight p q c z n) *
              (z ((n+1)*c)^p * (1-z ((n+1)*c))^q) :=
          mul_le_mul_of_nonneg_right ih.2 (mul_nonneg (pow_nonneg (unit _).1 _) (nonneg _))
        _ = _ := by unfold spineWeight; ring

/-- Lower-bound the normalizer on a boundary-safe event and transfer an upper
probability bound through the tilt. -/
theorem tilt_bound {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (R : Ω → ℝ) (integrable : Integrable R Q) (r0 : ∀ x, 0 ≤ R x) (r1 : ∀ x, R x ≤ 1)
    (A E : Set Ω) (measA : MeasurableSet A) (lo mass : ℝ) (hlo : 0 < lo) (hm : 0 < mass)
    (lower : ∀ x ∈ A, lo ≤ R x) (prob : mass ≤ Q.real A) :
    (∫ x in E, R x ∂Q) / (∫ x, R x ∂Q) ≤ Q.real E / (mass*lo) := by
  have denom : mass*lo ≤ ∫ x, R x ∂Q := calc
    _ ≤ Q.real A * lo := mul_le_mul_of_nonneg_right prob hlo.le
    _ = ∫ _ in A, lo ∂Q := by simp
    _ ≤ ∫ x in A, R x ∂Q := setIntegral_mono_on (integrable_const _).integrableOn
      integrable.integrableOn measA lower
    _ ≤ _ := setIntegral_le_integral integrable (ae_of_all _ r0)
  have num : (∫ x in E, R x ∂Q) ≤ Q.real E := calc
    _ ≤ ∫ _ in E, (1:ℝ) ∂Q := setIntegral_mono integrable.integrableOn
      (integrable_const _).integrableOn r1
    _ = _ := by simp
  exact div_le_div₀ (measureReal_nonneg) num (mul_pos hm hlo) denom

/-- The two usual normalizations of the rank differ by at most one mesh step. -/
theorem rank_conventions {D r : ℝ} (hD : 1 < D) (h1 : 1 ≤ r) (hd : r ≤ D) :
    |r/D - (r-1)/(D-1)| ≤ 1/D := by
  have d : 0 < D := by linarith
  have ds : 0 < D-1 := by linarith
  have e : r/D - (r-1)/(D-1) = (D-r) / (D*(D-1)) := by field_simp; ring
  rw [e, abs_of_nonneg (div_nonneg (sub_nonneg.mpr hd) (mul_pos d ds).le),
    div_le_div_iff₀ (mul_pos d ds) d]
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) d.le]

/-- An explicit exponentially decaying bound for the actual extension counts
implies the source conjecture. The probability estimate is a hypothesis here. -/
theorem conjecture61_of_tail_bound
    (bound : ∀ (m a b : ℕ), 1 ≤ a → a < b → b ≤ m → ∀ ε : ℝ, 0 < ε →
      ∃ C κ : ℝ, 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
        badFraction (a-1) (m-b) (b-a) n ε ≤ C * Real.exp (-κ * (n:ℝ))) : Conjecture61 := by
  intro m a b ha hab hbm ε hε
  obtain ⟨C, κ, hκ, h⟩ := bound m a b ha hab hbm ε hε
  have decay : Tendsto (fun n : ℕ => Real.exp (-κ * (n:ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hκ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using decay.const_mul C) (Eventually.of_forall fun n => badFraction_nonneg _ _ _ n _) h

end
end LeeSah
