import SolvedMath.RandomInversionLocalization
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.GCongr

namespace RandomInversionConnectivity
open Finset Filter
open scoped Topology
noncomputable section

theorem probability_not {n} (P : Perm n → Prop) :
    probability (fun π => ¬P π) = 1-probability P := by
  classical
  unfold probability
  calc
    _ = average (fun π : Perm n => 1-(if P π then (1:ℝ) else 0)) := by
      congr 1
      funext π
      by_cases pp : P π <;> simp [pp]
    _ = _ := by rw [average_sub,average_const]

theorem probability_flip {n} (P : Perm n → Prop) :
    probability (fun π => P (flip π)) = probability P := by
  classical
  unfold probability average
  congr 1
  exact Equiv.sum_comp (flipEquiv n) (fun π => if P π then 1 else (0:ℝ))

theorem equalityProbability_eq (n : Nat) :
    equalityProbability n = probability (fun π : Perm n => vertexConnectivity π = minimumDegree π) := by
  classical
  simp only [equalityProbability,probability,average,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  congr 1
  apply sum_congr rfl
  intro π _
  by_cases e : vertexConnectivity π = minimumDegree π <;> simp [e]

private theorem fail_four_le {n} (P Q R S : Perm n → Prop) :
    probability (fun π => ¬(P π ∧ Q π ∧ R π ∧ S π)) ≤
    probability (fun π => ¬P π) + probability (fun π => ¬Q π) +
    probability (fun π => ¬R π) + probability (fun π => ¬S π) := by
  classical
  unfold probability
  rw [←average_add,←average_add,←average_add]
  apply average_mono
  intro π
  by_cases p : P π <;> by_cases q : Q π <;> by_cases r : R π <;> by_cases s : S π <;>
    norm_num [p,q,r,s]

theorem unsafe_probability {n} (hn : 2≤n) (b l : Nat) (hl : 0 < l)
    (positive : 0 < hitMean (initial n b) (initial n b))
    (bulk : 4*(b:ℝ) ≤ hitMean (initial n (32*b)) (bulkColumns n b))
    (bp : 0 < b) :
    probability (fun π : Perm n => ¬SafeCorner π b l) ≤
      4 / hitMean (initial n b) (initial n b) +
      4 / hitMean (initial n (32*b)) (bulkColumns n b) +
      hitMean (initial n (34*b)) (initial n (34*b)) / l +
      ((nearPairs n (34*b) (2*l)).card : ℝ)^2 / ((n:ℝ)*(n-1)) := by
  have bpos : (0:ℝ) < b := by exact_mod_cast bp
  have first := hits_lower_tail hn (initial n b) (initial n b) positive
  have second := hits_lower_tail hn (initial n (32*b)) (bulkColumns n b) (by linarith)
  have third := hits_upper_tail (by omega : 0<n) (initial n (34*b)) (initial n (34*b)) hl
  let pairs := nearPairs n (34*b) (2*l)
  have fourth : probability (fun π : Perm n => pairHits π pairs pairs ≠ 0) ≤
      (pairs.card:ℝ)^2/((n:ℝ)*(n-1)) := by
    have h := markov (fun π : Perm n => pairHits π pairs pairs ≠ 0)
      (fun π => (pairHits π pairs pairs:ℝ)) (a := 1) (by norm_num) (fun _ => by positivity)
      (fun _ hp => by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp)
    simpa [mean_pairHits hn pairs pairs (fun p hp => near_distinct p hp) (fun p hp => near_distinct p hp),pow_two] using h
  let empty := fun π : Perm n => ¬0 < hits π (initial n b) (initial n b)
  let sparse := fun π : Perm n => ¬2*b < hits π (initial n (32*b)) (bulkColumns n b)
  have e : probability empty ≤ _ := (probability_mono (Q := fun π : Perm n =>
      2*(hits π (initial n b) (initial n b):ℝ) ≤ hitMean (initial n b) (initial n b))
    (by intro π hp; have z : hits π (initial n b) (initial n b)=0 := Nat.eq_zero_of_not_pos hp
        simpa [z] using positive.le)).trans first
  have f : probability sparse ≤ _ := (probability_mono (Q := fun π : Perm n =>
      2*(hits π (initial n (32*b)) (bulkColumns n b):ℝ) ≤
      hitMean (initial n (32*b)) (bulkColumns n b)) (by
    intro π h
    have v : hits π (initial n (32*b)) (bulkColumns n b) ≤ 2*b := Nat.le_of_not_gt h
    have v' : (hits π (initial n (32*b)) (bulkColumns n b):ℝ) ≤ 2*(b:ℝ) := by exact_mod_cast v
    linarith)).trans second
  have g := (probability_mono (P := fun π : Perm n => ¬ hits π (initial n (34*b)) (initial n (34*b)) ≤ l)
    (Q := fun π => l ≤ hits π (initial n (34*b)) (initial n (34*b)))
    (fun _ h => Nat.le_of_lt (Nat.lt_of_not_ge h))).trans third
  exact (fail_four_le ..).trans (add_le_add (add_le_add (add_le_add e f) g) fourth)

theorem bad_probability_le {n b l : Nat} :
    1-equalityProbability n ≤ 2*probability (fun π : Perm n => ¬SafeCorner π b l) := by
  rw [equalityProbability_eq,←probability_not]
  have inc := probability_mono (P := fun π : Perm n => ¬vertexConnectivity π = minimumDegree π)
    (Q := fun π => ¬SafeCorner π b l ∨ ¬SafeCorner (flip π) b l)
    (by intro π h; by_cases z : SafeCorner π b l
        · exact Or.inr (fun rev => h (equality_of_safe_corners z rev))
        · exact Or.inl z)
  have ub := inc.trans (probability_or_le ..)
  have flip := probability_flip (n := n) (fun π => ¬SafeCorner π b l)
  linarith


private theorem bulk_card {n b : Nat} (small : n/2+2*b < n) :
    (bulkColumns n b).card = n-(n/2+2*b) := by
  simp [bulkColumns,card_sdiff_of_subset (subset_univ _),card_initial small]

/-- An explicit choice of four rectangle tests produces a failure bound
tending to zero. The threshold is intentionally coarse. -/
theorem error_eventually (t : Nat) (ht : 1 ≤ t) :
    ∀ᶠ n : Nat in atTop, 1-equalityProbability n ≤ 14/(t:ℝ) := by
  let l := 5000*t^3
  filter_upwards [eventually_ge_atTop ((80*t)^2),
    eventually_ge_atTop (1+4624*t^3*(4*l+1)^2)] with n hn hbig
  let s := n.sqrt
  let b := t*(s+1)
  have ts : 80*t ≤ s := Nat.le_sqrt'.mpr hn
  have s1 : 1 ≤ s := by omega
  have sqlo : s^2 ≤ n := Nat.sqrt_le' n
  have sqhi : n < (s+1)^2 := Nat.lt_succ_sqrt' n
  have twice : s+1 ≤ 2*s := by omega
  have space : 40*b ≤ n := by
    calc
      40*b = 40*t*(s+1) := by dsimp [b]; ring
      _ ≤ 40*t*(2*s) := Nat.mul_le_mul_left _ twice
      _ = 80*t*s := by ring
      _ ≤ s*s := Nat.mul_le_mul_right s ts
      _ ≤ n := by simpa only [pow_two] using sqlo
  have bp : 0 < b := by dsimp [b]; positivity
  have lp : 0 < l := by dsimp [l]; positivity
  have n2 : 2 ≤ n := by omega
  have np : (0:ℝ) < n := by positivity
  have tp : (0:ℝ) < t := by positivity
  have bp' : (0:ℝ) < b := by positivity
  have lp' : (0:ℝ) < l := by positivity
  have nprev : 0 < (n:ℝ)-1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast n2
    linarith
  have tr : (1:ℝ) ≤ t := by exact_mod_cast ht
  have br : (b:ℝ) = (t:ℝ)*((s:ℝ)+1) := by simp [b]
  have lr : (l:ℝ) = 5000*(t:ℝ)^3 := by simp [l]
  have sr : (1:ℝ) ≤ s := by exact_mod_cast s1
  have srlo : (s:ℝ)^2 ≤ n := by exact_mod_cast sqlo
  have srhi : (n:ℝ) ≤ ((s:ℝ)+1)^2 := by exact_mod_cast sqhi.le
  have sqrtBound : ((s:ℝ)+1)^2 ≤ 4*(n:ℝ) := by
    have h := mul_self_le_mul_self (by positivity : 0 ≤ (s:ℝ)+1)
      (by linarith : (s:ℝ)+1 ≤ 2*s)
    nlinarith
  have bmean : (t:ℝ)^2 ≤ hitMean (initial n b) (initial n b) := by
    unfold hitMean
    rw [card_initial (by omega : b<n),br]
    apply (le_div_iff₀ np).mpr
    calc
      _ ≤ (t:ℝ)^2*((s:ℝ)+1)^2 := mul_le_mul_of_nonneg_left srhi (sq_nonneg _)
      _ = _ := by ring
  have wb : hitMean (initial n (34*b)) (initial n (34*b)) ≤ 4624*(t:ℝ)^2 := by
    unfold hitMean
    rw [card_initial (by omega : 34*b<n)]
    push_cast
    rw [br]
    apply (div_le_iff₀ np).mpr
    have h := mul_le_mul_of_nonneg_left sqrtBound (by positivity : 0 ≤ 1156*(t:ℝ)^2)
    nlinarith only [h]
  have highcol : n ≤ 8*(bulkColumns n b).card := by rw [bulk_card (by omega)]; omega
  have highreal : (n:ℝ) ≤ 8*((bulkColumns n b).card:ℝ) := by exact_mod_cast highcol
  have bulk : 4*(b:ℝ) ≤ hitMean (initial n (32*b)) (bulkColumns n b) := by
    unfold hitMean
    rw [card_initial (by omega : 32*b<n)]
    apply (le_div_iff₀ np).mpr
    push_cast
    have h := mul_le_mul_of_nonneg_left highreal (by positivity : 0 ≤ 4*(b:ℝ))
    nlinarith only [h]
  have bhpos : 0 < hitMean (initial n b) (initial n b) :=
    lt_of_lt_of_le (by positivity) bmean
  have highpos : 0 < hitMean (initial n (32*b)) (bulkColumns n b) := by linarith
  have first : 4/hitMean (initial n b) (initial n b) ≤ 4/(t:ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) tp (by nlinarith [sq_nonneg ((t:ℝ)-1)])
  have bge : (t:ℝ) ≤ b := by
    rw [br]
    nlinarith [mul_nonneg tp.le (by positivity : 0 ≤ (s:ℝ))]
  have second : 4/hitMean (initial n (32*b)) (bulkColumns n b) ≤ 1/(t:ℝ) :=
    (div_le_div_iff₀ highpos tp).mpr (by linarith)
  have third : hitMean (initial n (34*b)) (initial n (34*b))/(l:ℝ) ≤ 1/(t:ℝ) := by
    apply (div_le_div_iff₀ lp' tp).mpr
    rw [lr]
    have h := mul_le_mul_of_nonneg_right wb tp.le
    nlinarith [pow_pos tp 3]
  let pairs := nearPairs n (34*b) (2*l)
  have num : (pairs.card:ℝ) ≤ (34*(b:ℝ))*(4*(l:ℝ)+1) := by
    have nat : pairs.card ≤ (34*b)*(4*l+1) := by
      simpa only [←Nat.mul_assoc,show 2*2=4 by decide] using card_near n (34*b) (2*l)
    exact_mod_cast nat
  have last : (pairs.card:ℝ)^2 / ((n:ℝ)*(n-1)) ≤ 1/(t:ℝ) := by
    calc
      _ ≤ ((34*(b:ℝ))*(4*(l:ℝ)+1))^2/((n:ℝ)*(n-1)) := by gcongr
      _ = hitMean (initial n (34*b)) (initial n (34*b)) * (4*(l:ℝ)+1)^2/((n:ℝ)-1) := by
        unfold hitMean
        rw [card_initial (by omega : 34*b<n)]
        push_cast
        field_simp
      _ ≤ (4624*(t:ℝ)^2)*(4*(l:ℝ)+1)^2/((n:ℝ)-1) := by gcongr
      _ ≤ 1/(t:ℝ) := by
        apply (div_le_div_iff₀ nprev tp).mpr
        have h : (1:ℝ)+4624*(t:ℝ)^3*(4*(l:ℝ)+1)^2 ≤ n := by exact_mod_cast hbig
        nlinarith only [h]
  have cornerBound := unsafe_probability n2 b l lp bhpos bulk bp
  have ub := bad_probability_le (n := n) (b := b) (l := l)
  change ((nearPairs n (34*b) (2*l)).card:ℝ)^2/((n:ℝ)*(n-1)) ≤ 1/(t:ℝ) at last
  calc
    _ ≤ _ := ub
    _ ≤ 2*(4/(t:ℝ)+1/t+1/t+1/t) := mul_le_mul_of_nonneg_left
      (cornerBound.trans (add_le_add (add_le_add (add_le_add first second) third) last)) (by norm_num)
    _ = _ := by ring

theorem verkama_connectivity : VerkamaQuestion := by
  unfold VerkamaQuestion
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨t,ht⟩ := exists_nat_gt (14/(1-a)+1)
    have gap : 0 < 1-a := by linarith
    have tg : 0 < (t:ℝ) := by
      have h : 0 < 14/(1-a) := by positivity
      linarith
    have one : 1 ≤ t := by exact_mod_cast (show 0 < (t:ℝ) from tg)
    have frac : 14/(t:ℝ) < 1-a := by
      apply (div_lt_iff₀ tg).mpr
      have h : 14/(1-a) < (t:ℝ) := by linarith
      have h' := (div_lt_iff₀ gap).mp h
      linarith
    filter_upwards [error_eventually t one] with n h
    linarith
  · intro a ha
    filter_upwards with n
    have h : probability (fun π : Perm n => vertexConnectivity π=minimumDegree π) ≤ 1 := by
      rw [←average_const (n:=n) 1]
      apply average_mono
      intro π
      split <;> norm_num
    rw [←equalityProbability_eq] at h
    exact h.trans_lt ha

end
end RandomInversionConnectivity
