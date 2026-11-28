import SolvedMath.RandomInversionConnectivity
import SolvedMath.RandomPatternDisplacements
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace RandomInversionConnectivity

open Finset
noncomputable section

private def oneMark {n} (x : Fin n) : Fin 1 ↪ Fin n :=
  ⟨fun _ => x,fun _ _ _ => Subsingleton.elim ..⟩

private def twoMarks {n} (x y : Fin n) (h : x ≠ y) : Fin 2 ↪ Fin n :=
  ⟨![x,y],by intro i j eq; fin_cases i <;> fin_cases j <;> simp_all⟩

theorem one_assignment {n} (x v : Fin n) :
    (univ.filter (fun π : Perm n => π x=v)).card = (n-1).factorial := by
  have z := DistinctPermutationPatterns.prescribed_assignment_count (oneMark x) (oneMark v)
  convert z using 2
  ext π
  simp only [mem_filter,mem_univ,true_and]
  exact ⟨fun h _ => h,fun h => h 0⟩

theorem two_assignments {n} {x y v w : Fin n} (hxy : x≠y) (hvw : v≠w) :
    (univ.filter (fun π : Perm n => π x=v ∧ π y=w)).card = (n-2).factorial := by
  have z := DistinctPermutationPatterns.prescribed_assignment_count (twoMarks x y hxy) (twoMarks v w hvw)
  convert z using 2
  ext π
  simp only [mem_filter,mem_univ,true_and]
  constructor
  · intro h j
    fin_cases j
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0,h 1⟩

def hits {n} (π : Perm n) (rows cols : Finset (Fin n)) : Nat :=
  (rows.filter (fun x => π x ∈ cols)).card

def pairHits {n} (π : Perm n) (rows cols : Finset (Fin n × Fin n)) : Nat :=
  (rows.filter (fun p => (π p.1,π p.2) ∈ cols)).card

theorem sum_hits {n} (rows cols : Finset (Fin n)) :
    (∑ π : Perm n, hits π rows cols) = rows.card * cols.card * (n-1).factorial := by
  classical
  have inside (π : Perm n) (x : Fin n) :
      (if π x ∈ cols then 1 else 0 : Nat) = ∑ y ∈ cols, if π x=y then 1 else 0 := by
    simp
  have each (x : Fin n) : (∑ π : Perm n, if π x∈cols then 1 else 0 : Nat) =
      cols.card * (n-1).factorial := by
    simp_rw [inside]
    rw [sum_comm]
    simp_rw [← card_filter,one_assignment]
    simp
  simp only [hits,card_filter]
  rw [sum_comm]
  simp_rw [each]
  simp [Nat.mul_assoc]

theorem sum_pairHits {n} (rows cols : Finset (Fin n × Fin n))
    (dr : ∀ p ∈ rows, p.1 ≠ p.2) (dc : ∀ p ∈ cols, p.1 ≠ p.2) :
    (∑ π : Perm n, pairHits π rows cols) = rows.card * cols.card * (n-2).factorial := by
  classical
  have inside (π : Perm n) (p : Fin n × Fin n) :
      (if (π p.1,π p.2) ∈ cols then 1 else 0 : Nat) =
          ∑ v ∈ cols, if (π p.1,π p.2)=v then 1 else 0 := by simp
  have count (p : Fin n × Fin n) (hp : p ∈ rows) (v : Fin n × Fin n) (hv : v ∈ cols) :
      (∑ π : Perm n, if (π p.1,π p.2)=v then 1 else 0 : Nat) = (n-2).factorial := by
    rw [← card_filter]
    simpa only [Prod.ext_iff] using two_assignments (dr p hp) (dc v hv)
  have each (p : Fin n × Fin n) (hp : p ∈ rows) :
      (∑ π : Perm n, if (π p.1,π p.2)∈cols then 1 else 0 : Nat) =
          cols.card * (n-2).factorial := by
    simp_rw [inside]
    rw [sum_comm]
    calc
      _ = ∑ _v ∈ cols, (n-2).factorial := sum_congr rfl (count p hp)
      _ = _ := by simp
  simp only [pairHits,card_filter]
  rw [sum_comm]
  calc
    _ = ∑ _p ∈ rows, cols.card * (n-2).factorial := sum_congr rfl each
    _ = _ := by simp [Nat.mul_assoc]

theorem hit_second {n} (π : Perm n) (rows cols : Finset (Fin n)) :
    (hits π rows cols)^2 = hits π rows cols + pairHits π rows.offDiag cols.offDiag := by
  classical
  let s := rows.filter (fun x => π x ∈ cols)
  have eq : rows.offDiag.filter (fun p => (π p.1,π p.2)∈cols.offDiag) = s.offDiag := by
    ext p
    simp only [mem_filter,mem_offDiag,s]
    have distinct : p.1 ≠ p.2 → π p.1 ≠ π p.2 := fun h e => h (π.injective e)
    tauto
  change s.card^2 = s.card + _
  unfold pairHits
  rw [eq,offDiag_card,pow_two]
  by_cases h : s.card=0
  · simp [h]
  · have ge := Nat.mul_le_mul_left s.card (show 1 ≤ s.card by omega)
    omega


def average {n} (f : Perm n → ℝ) : ℝ := (∑ π, f π) / n.factorial

def probability {n} (P : Perm n → Prop) : ℝ := by
  classical exact average fun π => if P π then 1 else 0

theorem average_mono {n} {f g : Perm n → ℝ} (h : ∀ π, f π ≤ g π) : average f ≤ average g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun π _ => h π)) (by positivity)

theorem average_add {n} (f g : Perm n → ℝ) :
    average (fun π => f π + g π) = average f + average g := by
  simp only [average,sum_add_distrib,add_div]

theorem average_sub {n} (f g : Perm n → ℝ) :
    average (fun π => f π - g π) = average f - average g := by
  simp only [average,sum_sub_distrib,sub_div]

theorem average_mul {n} (a : ℝ) (f : Perm n → ℝ) :
    average (fun π => a*f π) = a*average f := by
  simp only [average,← mul_sum,mul_div_assoc]

theorem average_const {n} (a : ℝ) : average (fun _ : Perm n => a) = a := by
  simp [average,Fintype.card_perm,Nat.factorial_ne_zero]

private theorem factorial_one {n : Nat} (hn : 0 < n) :
    (n.factorial : ℝ) = n * ((n-1).factorial : Nat) := by
  cases n with
  | zero => omega
  | succ n => simp [Nat.factorial_succ]

private theorem factorial_two {n : Nat} (hn : 2 ≤ n) :
    (n.factorial : ℝ) = n * ((n : ℝ)-1) * ((n-2).factorial : Nat) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le' hn
  simp [Nat.factorial_succ, Nat.cast_add]
  ring

def hitMean {n} (r c : Finset (Fin n)) : ℝ := (r.card : ℝ)*c.card/n

theorem mean_hits {n} (hn : 0 < n) (r c : Finset (Fin n)) :
    average (fun π => (hits π r c : ℝ)) = hitMean r c := by
  simp only [average,←Nat.cast_sum,sum_hits,Nat.cast_mul,hitMean]
  rw [factorial_one hn]
  have hn' : (n:ℝ)≠0 := by positivity
  have hf : (((n-1).factorial : Nat):ℝ) ≠ 0 := by positivity
  field_simp

theorem mean_pairHits {n} (hn : 2 ≤ n) (r c : Finset (Fin n × Fin n))
    (dr : ∀ p ∈ r, p.1≠p.2) (dc : ∀ p ∈ c, p.1≠p.2) :
    average (fun π => (pairHits π r c : ℝ)) = (r.card : ℝ)*c.card/(n*((n:ℝ)-1)) := by
  simp only [average,←Nat.cast_sum,sum_pairHits r c dr dc,Nat.cast_mul]
  rw [factorial_two hn]
  have hn' : (n:ℝ) ≠ 0 := by positivity
  have hg : (n:ℝ)-1 ≠ 0 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hf : (((n-2).factorial : Nat):ℝ) ≠ 0 := by positivity
  field_simp

/-- Sampling without replacement has variance at most its mean. -/
theorem hit_variance {n} (hn : 2 ≤ n) (r c : Finset (Fin n)) :
    average (fun π => ((hits π r c : ℝ)-hitMean r c)^2) ≤ hitMean r c := by
  have hn' : (0:ℝ)<n := by positivity
  have hn1 : 0 < (n:ℝ)-1 := by
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have mean := mean_hits (by omega : 0<n) r c
  have moment := mean_pairHits hn r.offDiag c.offDiag
    (fun _ h => (mem_offDiag.mp h).2.2) (fun _ h => (mem_offDiag.mp h).2.2)
  have ident : average (fun π => (hits π r c : ℝ)^2) =
      hitMean r c + average (fun π => (pairHits π r.offDiag c.offDiag : ℝ)) := by
    rw [←mean,←average_add]
    congr 1
    funext π
    exact_mod_cast hit_second π r c
  simp only [offDiag_card,←Nat.mul_sub_one,Nat.cast_mul] at moment
  have rle : ((r.card-1:Nat):ℝ) ≤ r.card := by exact_mod_cast Nat.sub_le r.card 1
  have cle : ((c.card-1:Nat):ℝ)*n ≤ c.card*((n:ℝ)-1) := by
    by_cases z : c.card = 0
    · simp [z]
    rw [Nat.cast_sub (by omega : 1 ≤ c.card)]
    have size : c.card ≤ n := by simpa using card_le_univ c
    have size' : (c.card:ℝ) ≤ n := by exact_mod_cast size
    push_cast
    linarith
  have rate : ((r.card-1:Nat):ℝ)*((c.card-1:Nat):ℝ)/((n:ℝ)-1) ≤ hitMean r c := by
    apply (div_le_div_iff₀ hn1 hn').mpr
    calc
      _ = ((r.card-1:Nat):ℝ)*(((c.card-1:Nat):ℝ)*n) := by ring
      _ ≤ (r.card:ℝ)*(c.card*((n:ℝ)-1)) := mul_le_mul rle cle (by positivity) (by positivity)
      _ = _ := by ring
  have prod : average (fun π => (pairHits π r.offDiag c.offDiag : ℝ)) ≤
      hitMean r c * hitMean r c := by
    rw [moment]
    calc
      _ = hitMean r c * (((r.card-1:Nat):ℝ)*((c.card-1:Nat):ℝ)/((n:ℝ)-1)) := by
        unfold hitMean
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left rate (by unfold hitMean; positivity)
  have ex : (fun π : Perm n => ((hits π r c : ℝ)-hitMean r c)^2) =
      (fun π => ((hits π r c : ℝ)^2 - (2*hitMean r c)*(hits π r c : ℝ)) + (hitMean r c)^2) := by
    funext π
    ring
  rw [ex,average_add,average_sub,average_mul,average_const,ident,mean]
  nlinarith


theorem probability_mono {n} {P Q : Perm n → Prop} (h : ∀ π, P π → Q π) :
    probability P ≤ probability Q := by
  classical
  apply average_mono
  intro π
  by_cases hp : P π
  · simp [hp,h π hp]
  · simp [hp]
    split <;> norm_num

theorem probability_or_le {n} (P Q : Perm n → Prop) :
    probability (fun π => P π ∨ Q π) ≤ probability P + probability Q := by
  classical
  unfold probability
  rw [←average_add]
  apply average_mono
  intro π
  by_cases hp : P π <;> by_cases hq : Q π <;> simp [hp,hq]

theorem markov {n} (P : Perm n → Prop) (f : Perm n → ℝ) {a : ℝ}
    (ha : 0<a) (nonneg : ∀ π, 0 ≤ f π) (witness : ∀ π, P π → a ≤ f π) :
    probability P ≤ average f / a := by
  classical
  apply (le_div_iff₀ ha).2
  rw [mul_comm,probability,←average_mul]
  apply average_mono
  intro π
  by_cases hp : P π
  · simpa [hp] using witness π hp
  · simpa [hp] using nonneg π

theorem hits_upper_tail {n} (hn : 0<n) (r c : Finset (Fin n)) {l : Nat} (hl : 0<l) :
    probability (fun π => l ≤ hits π r c) ≤ hitMean r c / l := by
  rw [←mean_hits hn]
  apply markov _ _ (by positivity) (fun _ => by positivity)
  intro π h
  exact_mod_cast h

theorem hits_lower_tail {n} (hn : 2≤n) (r c : Finset (Fin n)) (hm : 0<hitMean r c) :
    probability (fun π => 2*(hits π r c : ℝ) ≤ hitMean r c) ≤ 4/hitMean r c := by
  let μ := hitMean r c
  change probability (fun π => 2*(hits π r c : ℝ) ≤ μ) ≤ 4/μ
  have pos : 0 < μ := hm
  have h := markov (fun π : Perm n => 2*(hits π r c : ℝ) ≤ μ)
    (fun π => ((hits π r c : ℝ)-μ)^2) (a := (μ/2)^2) (by positivity) (fun _ => sq_nonneg _)
    (by
      intro π h
      have b : μ/2 ≤ μ-(hits π r c : ℝ) := by linarith
      have b' := mul_self_le_mul_self (by positivity : 0 ≤ μ/2) b
      nlinarith only [b'])
  calc
    _ ≤ _ := h
    _ ≤ μ/(μ/2)^2 := div_le_div_of_nonneg_right (hit_variance hn r c) (sq_nonneg _)
    _ = _ := by field_simp; norm_num

end
end RandomInversionConnectivity
