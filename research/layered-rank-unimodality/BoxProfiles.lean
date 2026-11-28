module

public import GreedyBoxes
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace LayeredRanks
open Finset

/-- Coefficients reflected about the half-integer C/2, weakly decreasing to its right. -/
structure Centered (C : ℤ) (f : ℤ → ℕ) : Prop where
  symm : ∀ r, f (C-r) = f r
  tail : ∀ r, C ≤ 2*r+1 → f (r+1) ≤ f r

private theorem Centered.later {C : ℤ} {f : ℤ → ℕ} (hf : Centered C f) {x y : ℤ}
    (hxy : x ≤ y) (hfar : C ≤ x+y) : f y ≤ f x := by
  let z := max x (C-x)
  have hz : z ≤ y := max_le hxy (by omega)
  have hcz : C ≤ 2*z := by dsimp [z]; omega
  have hstart : f z = f x := by
    dsimp [z]
    rcases le_total x (C-x) with h | h
    · rw [max_eq_right h, hf.symm]
    · rw [max_eq_left h]
  obtain ⟨d, hd⟩ := Int.le.dest hz
  have step (n : ℕ) : f (z+n) ≤ f z := by
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      rw [← add_assoc]
      exact (hf.tail _ (by omega)).trans ih
  have h := step d
  simpa [hd, hstart] using h

/-- Rank convolution by the consecutive integer interval from a through a+m. -/
def window (a : ℤ) (m : ℕ) (f : ℤ → ℕ) (r : ℤ) :=
  ∑ j ∈ range (m+1), f (r-a-j)

theorem window_slide (a : ℤ) (m : ℕ) (f : ℤ → ℕ) (r : ℤ) :
    window a m f (r+1) + f (r-a-m) = window a m f r + f (r+1-a) := by
  induction m with
  | zero => simp [window, add_comm]
  | succ m ih =>
    simp only [window, sum_range_succ] at ih ⊢
    push_cast
    rw [show r+1-a-(m+1:ℤ) = r-a-m by ring]
    omega

theorem Centered.window {C : ℤ} {f : ℤ → ℕ} (hf : Centered C f) (a : ℤ) (m : ℕ) :
    Centered (C+2*a+m) (LayeredRanks.window a m f) := by
  constructor
  · intro r
    unfold LayeredRanks.window
    rw [← Finset.sum_range_reflect (fun j : ℕ => f (r-a-j)) (m+1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hjm : j ≤ m := by simpa using (Finset.mem_range.1 hj)
    have heq : C+2*a+m-r-a-j = C - (r-a-((m+1-1-j : ℕ):ℤ)) := by
      simp [Nat.cast_sub hjm]
      ring
    rw [heq, hf.symm]
  · intro r hr
    have h := hf.later (x := r-a-m) (y := r+1-a) (by omega) (by omega)
    have eq := window_slide a m f r
    omega

def intervals : ℕ → List ℕ → List Bool → List (ℕ × ℕ)
  | bound, b::w, true::mask => (bound+1, b) :: intervals 0 w mask
  | bound, b::w, false::mask => intervals (max bound b) w mask
  | _, _, _ => []

def boxProfile : List (ℕ × ℕ) → ℤ → ℕ
  | [], r => if r = 0 then 1 else 0
  | (a,b)::rest, r => if a ≤ b then window a (b-a) (boxProfile rest) r else 0

def centers (pairs : List (ℕ × ℕ)) := (pairs.map (fun p => (p.1:ℤ)+p.2)).sum

theorem boxProfile_centered (pairs : List (ℕ × ℕ)) :
    Centered (centers pairs) (boxProfile pairs) := by
  induction pairs with
  | nil =>
    constructor
    · intro r
      simp [centers, boxProfile]
    · intro r h
      simp [centers] at h
      by_cases h0 : r+1 = 0
      · omega
      · simp [boxProfile, h0]
  | cons p pairs ih =>
    obtain ⟨a,b⟩ := p
    by_cases hab : a ≤ b
    · have h := ih.window (a:ℤ) (b-a)
      have hc : centers ((a,b)::pairs) = centers pairs + 2*(a:ℤ) + ((b-a:ℕ):ℤ) := by
        change (a:ℤ)+b+centers pairs = _
        rw [Nat.cast_sub hab]
        ring
      rw [hc]
      simpa [boxProfile, hab] using h
    · constructor <;> intros <;> simp [boxProfile, hab]

theorem centers_intervals (bound : ℕ) (w : List ℕ) (mask : List Bool) :
    centers (intervals bound w mask) = twiceCenter bound w mask := by
  induction w generalizing bound mask with
  | nil => simp [centers, intervals, twiceCenter]
  | cons b w ih =>
    cases mask with
    | nil => simp [centers, intervals, twiceCenter]
    | cons bit mask =>
      cases bit with
      | false => exact ih _ _
      | true =>
        simp only [intervals, twiceCenter]
        change ((bound+1:ℕ):ℤ)+b+centers (intervals 0 w mask) = _
        rw [ih]
        push_cast
        ring

/-- The integer-indexed slice also gives zero at negative ranks. -/
def wordSlice (S : Finset (List ℕ)) (r : ℤ) :=
  S.filter (fun u => (u.sum:ℤ) = r)

private theorem true_slice_card (bound b : ℕ) (w : List ℕ) (mask : List Bool) (r : ℤ) :
    (wordSlice (boxWords bound (b::w) (true::mask)) r).card =
      ∑ t ∈ Icc (bound+1) b, (wordSlice (boxWords 0 w mask) (r-t)).card := by
  let part (t : ℕ) := (wordSlice (boxWords 0 w mask) (r-t)).image (t :: ·)
  have split : wordSlice (boxWords bound (b::w) (true::mask)) r =
      (Icc (bound+1) b).biUnion part := by
    ext v
    cases v with
    | nil => simp [part, wordSlice, boxWords]
    | cons a u =>
      simp [part, wordSlice, boxWords]
      grind
  rw [split, Finset.card_biUnion]
  · apply sum_congr rfl
    intro t _
    apply card_image_of_injective
    intro v v' hv
    exact (List.cons.inj hv).2
  · intro t _ t' _ ht
    apply Finset.disjoint_left.2
    rintro v hv hv'
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨_, _, heq⟩ := Finset.mem_image.1 hv'
    exact ht (List.cons.inj heq).1.symm

theorem slice_card_eq_profile (bound : ℕ) (w : List ℕ) (mask : List Bool)
    (hm : mask.length = w.length) (r : ℤ) :
    (wordSlice (boxWords bound w mask) r).card = boxProfile (intervals bound w mask) r := by
  induction w generalizing bound mask r with
  | nil =>
    have he : mask = [] := List.length_eq_zero_iff.mp (by simpa using hm)
    subst mask
    simp only [wordSlice, boxWords, intervals, boxProfile, Finset.filter_singleton]
    by_cases h0 : r = 0 <;> simp [h0, eq_comm]
  | cons b w ih =>
    cases mask with
    | nil => simp at hm
    | cons bit mask =>
      have hm' : mask.length = w.length := by simpa using hm
      cases bit with
      | false => exact ih _ _ hm' r
      | true =>
        rw [true_slice_card]
        simp_rw [ih 0 mask hm']
        simp only [intervals, boxProfile]
        by_cases h : bound+1 ≤ b
        · simp [h, window]
          rw [show Icc (bound+1) b = Ico (bound+1) (b+1) by ext n; simp,
            Finset.sum_Ico_eq_sum_range]
          have hn : b+1-(bound+1) = b-(bound+1)+1 := by omega
          rw [hn]
          apply sum_congr rfl
          intro j _
          congr 1
          push_cast
          ring
        · have he : Icc (bound+1) b = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
          simp [h, he]

theorem boxCount_eq_profile (w : List ℕ) (mask : List Bool) (hm : mask.length = w.length)
    (r : ℕ) : boxCount w mask r = boxProfile (intervals 0 w mask) r := by
  simpa only [boxCount, wordSlice, Nat.cast_inj] using slice_card_eq_profile 0 w mask hm r

/-- Upper-tail decrease for actual distinct composition counts, to within one rank
of the version in which the final optional part is combined with full support. -/
theorem rankCount_upper_tail (w : List ℕ) (r : ℕ) (hr : w.sum+w.length ≤ 2*r+1) :
    rankCount w (r+1) ≤ rankCount w r := by
  rw [rankCount_eq_sum_boxes, rankCount_eq_sum_boxes]
  apply sum_le_sum
  intro mask hm
  have hlen := masks_length.1 hm
  rw [boxCount_eq_profile _ _ hlen, boxCount_eq_profile _ _ hlen]
  push_cast
  apply (boxProfile_centered _).tail
  rw [centers_intervals]
  have h := twiceCenter_le 0 w mask
  have hm' : mask.count true ≤ mask.length := List.count_le_length
  omega

private theorem window_add (a : ℤ) (m : ℕ) (f g : ℤ → ℕ) (r : ℤ) :
    window a m f r + window a m g r = window a m (fun t => f t + g t) r := by
  simp [window, sum_add_distrib]

private theorem last_optional (b : ℕ) (f : ℤ → ℕ) (r : ℤ) :
    (if 1 ≤ b then window 1 (b-1) f r else 0) + f r = window 0 b f r := by
  cases b with
  | zero => simp [window]
  | succ b =>
    simp only [show 1 ≤ b+1 by omega, ↓reduceIte, Nat.succ_sub_one, window, sub_zero]
    rw [Finset.sum_range_succ' (fun j : ℕ => f (r-j)) (b+1)]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
    congr 1
    apply sum_congr rfl
    intro j _
    congr 1
    ring

private theorem optional_profile (pairs : List (ℕ × ℕ)) (b : ℕ) (r : ℤ) :
    boxProfile (pairs ++ [(1,b)]) r + boxProfile pairs r =
      boxProfile (pairs ++ [(0,b)]) r := by
  induction pairs generalizing r with
  | nil => simpa [boxProfile] using last_optional b (boxProfile []) r
  | cons p rest ih =>
    obtain ⟨a,d⟩ := p
    by_cases h : a ≤ d
    · simp only [List.cons_append, boxProfile, h, ↓reduceIte]
      rw [window_add]
      congr 2
      funext t
      exact ih t
    · simp [boxProfile, h]

private theorem prefix_intervals (w : List ℕ) (b : ℕ) (bit : Bool) :
    intervals 0 (w++[b]) (List.replicate w.length true ++ [bit]) =
      w.map (fun a => (1,a)) ++ (if bit then [(1,b)] else []) := by
  induction w with
  | nil => cases bit <;> rfl
  | cons a w ih => simp [List.replicate_succ, intervals, ih]

private theorem optional_centers (w : List ℕ) (b : ℕ) :
    centers (w.map (fun a => (1,a)) ++ [(0,b)]) = (w.sum:ℤ)+w.length+b := by
  induction w with
  | nil => simp [centers]
  | cons a w ih =>
    change (1:ℤ)+a+centers (w.map (fun a => (1,a)) ++ [(0,b)]) = _
    rw [ih]
    simp
    ring

/-- The sharp upper-tail bound with the empty final choice combined with full
support. The bound is on the cardinalities of the actual distinct composition slices. -/
theorem rankCount_sharp_upper_tail (w : List ℕ) (r : ℕ) (hr : w.sum+w.length ≤ 2*r+2) :
    rankCount w (r+1) ≤ rankCount w r := by
  classical
  induction w using List.reverseRecOn with
  | nil =>
    rw [rankCount_eq_sum_boxes, rankCount_eq_sum_boxes]
    simp [masks, boxCount, boxWords, Finset.filter_singleton]
  | append_singleton u b _ =>
    let yes := List.replicate u.length true ++ [true]
    let no := List.replicate u.length true ++ [false]
    let W := u++[b]
    let S := masks W
    have hy : yes ∈ S := masks_length.2 (by simp [W,yes])
    have hn : no ∈ S := masks_length.2 (by simp [W,no])
    have hny : no ≠ yes := by simp [no, yes]
    have hne : no ∈ S.erase yes := mem_erase.2 ⟨hny, hn⟩
    let rest := (S.erase yes).erase no
    have split (n : ℕ) : rankCount W n =
        (∑ m ∈ rest, boxCount W m n) + (boxCount W yes n + boxCount W no n) := by
      rw [rankCount_eq_sum_boxes]
      change ∑ m ∈ S, boxCount W m n = _
      rw [← sum_erase_add _ _ hy, ← sum_erase_add _ _ hne]
      dsimp only [rest]
      omega
    have hs : ∀ m ∈ rest, boxCount W m (r+1) ≤ boxCount W m r := by
      intro m hm
      obtain ⟨_, hy'⟩ := Finset.mem_erase.1 hm
      obtain ⟨hy', hmem⟩ := Finset.mem_erase.1 hy'
      have hl := masks_length.1 hmem
      have hlt : m.count true < m.length := by
        have hle : m.count true ≤ m.length := List.count_le_length
        by_contra! h
        have eq := List.replicate_count_eq_of_count_eq_length (le_antisymm hle h)
        apply hy'
        rw [← eq]
        have size : m.count true = u.length+1 := by simpa [W] using (le_antisymm hle h).trans hl
        rw [size]
        exact List.replicate_succ'
      rw [boxCount_eq_profile _ _ hl, boxCount_eq_profile _ _ hl]
      push_cast
      apply (boxProfile_centered _).tail
      rw [centers_intervals]
      have h := twiceCenter_le 0 W m
      change W.sum+W.length ≤ 2*r+2 at hr
      omega
    let P := u.map (fun a => (1,a)) ++ [(0,b)]
    have pair (n : ℕ) : boxCount W yes n + boxCount W no n = boxProfile P n := by
      rw [boxCount_eq_profile _ _ (masks_length.1 hy), boxCount_eq_profile _ _ (masks_length.1 hn)]
      dsimp only [W, yes, no, P]
      rw [prefix_intervals, prefix_intervals]
      simpa using optional_profile (u.map (fun a => (1,a))) b n
    change rankCount W (r+1) ≤ rankCount W r
    rw [split, split, pair, pair]
    apply Nat.add_le_add (sum_le_sum hs)
    push_cast
    apply (boxProfile_centered _).tail
    dsimp only [P]
    rw [optional_centers]
    simp at hr
    omega

end LayeredRanks
