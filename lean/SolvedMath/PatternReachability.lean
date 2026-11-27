import SolvedMath.PatternSeparator

/-! Weak comparison in a stack from two maps on the ranks of a single pattern. -/

namespace SolvedMath.PatternSeparator

structure Compatible {k} (p : Permutation k) (m d : Nat) : Prop where
  length_eq : k = d + m
  stride_pos : 0 < d
  same_order : ∀ i < m, ∀ q < m,
    p.rank (d+i) ≤ p.rank (d+q) ↔ p.rank i ≤ p.rank q

def Weak {k} (p : Permutation k) (d j x y : Nat) : Prop :=
  x = y ∨ Below p d j x y

theorem Weak.trans {k} {p : Permutation k} {d j x y z}
    (h : Weak p d j x y) (h' : Weak p d j y z) : Weak p d j x z := by
  rcases h with rfl | h
  · exact h'
  rcases h' with rfl | h'
  · exact Or.inr h
  exact Or.inr (h.trans h')

theorem Weak.inWindow {k} (p : Permutation k) {d j t i l}
    (ht : t < j) (hi : i < k) (hl : l < k) (hr : p.rank i ≤ p.rank l) :
    Weak p d j (d*t+i) (d*t+l) := by
  rcases Nat.eq_or_lt_of_le hr with h | h
  · exact Or.inl (congrArg (fun a => d*t+a) (p.injective hi hl h))
  · exact Or.inr (.window t i l ht hi hl h)

/-- The least destination rank attainable through an eligible shared position.
The sentinel k represents an empty upper set. -/
def transfer (k : Nat) (src dst : Nat → Nat) (r : Nat) : Nat → Nat
  | 0 => k
  | m+1 => if r ≤ src m then min (transfer k src dst r m) (dst m)
           else transfer k src dst r m

theorem transfer_bounded {k src dst r} (m : Nat) : transfer k src dst r m ≤ k := by
  induction m with
  | zero => exact Nat.le_refl _
  | succ m ih =>
    unfold transfer
    split
    · exact Nat.le_trans (Nat.min_le_left ..) ih
    · exact ih

theorem transfer_mono {k src dst r s m} (h : r ≤ s) :
    transfer k src dst r m ≤ transfer k src dst s m := by
  induction m with
  | zero => exact Nat.le_refl _
  | succ m ih =>
    simp only [transfer]
    split <;> split <;> omega

theorem transfer_le_iff {k src dst r s m} (hs : s < k) :
    transfer k src dst r m ≤ s ↔ ∃ i < m, r ≤ src i ∧ dst i ≤ s := by
  induction m with
  | zero => simp [transfer]; omega
  | succ m ih =>
    constructor
    · intro h
      unfold transfer at h
      split at h
      · by_cases b : dst m ≤ s
        · exact ⟨m, by omega, ‹r ≤ src m›, b⟩
        · obtain ⟨i, hi, hsrc, hdst⟩ := ih.mp (by omega)
          exact ⟨i, by omega, hsrc, hdst⟩
      · obtain ⟨i, hi, hsrc, hdst⟩ := ih.mp h
        exact ⟨i, by omega, hsrc, hdst⟩
    · rintro ⟨i, hi, hsrc, hdst⟩
      by_cases he : i = m
      · subst i
        simp only [transfer, ite_eq_left hsrc]
        exact Nat.le_trans (Nat.min_le_right ..) hdst
      · have prev := ih.mpr ⟨i, by omega, hsrc, hdst⟩
        unfold transfer
        split <;> omega

def forward {k} (p : Permutation k) (m d r : Nat) : Nat :=
  transfer k (fun i => p.rank (d+i)) p.rank r m

def backward {k} (p : Permutation k) (m d r : Nat) : Nat :=
  transfer k p.rank (fun i => p.rank (d+i)) r m

def steps (f : Nat → Nat) : Nat → Nat → Nat
  | 0, r => r
  | n+1, r => f (steps f n r)

def threshold {k} (p : Permutation k) (m d s r t : Nat) : Nat :=
  if s ≤ t then steps (forward p m d) (t-s) r
  else steps (backward p m d) (s-t) r

namespace Compatible

variable {k m d : Nat} {p : Permutation k} (H : Compatible p m d)
include H

private theorem forward_anchor {i r} (hi : i < m) :
    forward p m d r ≤ p.rank i ↔ r ≤ p.rank (d+i) := by
  have hk := H.length_eq
  rw [forward, transfer_le_iff (p.bounded (by omega : i < k))]
  constructor
  · rintro ⟨q,hq,hr,he⟩
    exact Nat.le_trans hr ((H.same_order q hq i hi).mpr he)
  · exact fun h => ⟨i,hi,h,Nat.le_refl _⟩

private theorem backward_anchor {i r} (hi : i < m) :
    backward p m d r ≤ p.rank (d+i) ↔ r ≤ p.rank i := by
  have hk := H.length_eq
  rw [backward, transfer_le_iff (p.bounded (by omega : d+i < k))]
  constructor
  · rintro ⟨q,hq,hr,he⟩
    exact Nat.le_trans hr ((H.same_order q hq i hi).mp he)
  · exact fun h => ⟨i,hi,h,Nat.le_refl _⟩

private theorem adjacent (s r t : Nat) {i} (hi : i < m) :
    threshold p m d s r t ≤ p.rank (d+i) ↔ threshold p m d s r (t+1) ≤ p.rank i := by
  by_cases h : s ≤ t
  · have h' : s ≤ t+1 := by omega
    simp only [threshold, ite_eq_left h, ite_eq_left h']
    rw [show t+1-s = (t-s)+1 by omega, steps, H.forward_anchor hi]
  · have ht : t < s := by omega
    by_cases eq : s = t+1
    · subst s
      simp [threshold, h, steps, H.backward_anchor hi]
    · have h' : ¬ s ≤ t+1 := by omega
      simp only [threshold, ite_eq_right h, ite_eq_right h']
      rw [show s-t = (s-(t+1))+1 by omega, steps, H.backward_anchor hi]

/-- A shared physical position has the same upper-set membership in every
representation. Normalization may cross several windows when the overlap is long. -/
private theorem normalize (s r : Nat) (i : Nat) (hi : i < k) (t : Nat) :
    threshold p m d s r t ≤ p.rank i ↔
      threshold p m d s r ((d*t+i)/d) ≤ p.rank ((d*t+i)%d) := by
  by_cases h : i < d
  · simp [Nat.mul_add_div H.stride_pos, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]
  · have hk := H.length_eq
    have hd := H.stride_pos
    let q := i-d
    have eq : i = d+q := by dsimp [q]; omega
    have hq : q < m := by omega
    have hqk : q < k := by omega
    have hre := H.adjacent s r t hq
    rw [← eq] at hre
    rw [hre, normalize s r q hqk (t+1)]
    rw [Nat.mul_succ, Nat.add_assoc, ← eq]
termination_by i
decreasing_by omega

private def upperAt (p : Permutation k) (m d s r x : Nat) : Prop :=
  threshold p m d s r (x/d) ≤ p.rank (x%d)

private theorem upward {s r j x y} (h : Below p d j x y) :
    upperAt p m d s r x → upperAt p m d s r y := by
  induction h with
  | window t i l _ hi hl hr =>
    exact fun hx => (H.normalize s r l hl t).mp
      (Nat.le_trans ((H.normalize s r i hi t).mpr hx) (Nat.le_of_lt hr))
  | trans _ _ xy yz => exact fun hx => yz (xy hx)

private theorem necessary {j s t i l} (hi : i < k) (hl : l < k)
    (path : Weak p d j (d*s+i) (d*t+l)) :
    threshold p m d s (p.rank i) t ≤ p.rank l := by
  have start : upperAt p m d s (p.rank i) (d*s+i) :=
    (H.normalize s (p.rank i) i hi s).mp (by simp [threshold, steps])
  apply (H.normalize s (p.rank i) l hl t).mpr
  rcases path with eq | strict
  · exact eq ▸ start
  · exact H.upward strict start

private theorem goRight {j s i} (hi : i < k) (n : Nat) (hn : s+n < j)
    {l} (hl : l < k) (hr : steps (forward p m d) n (p.rank i) ≤ p.rank l) :
    Weak p d j (d*s+i) (d*(s+n)+l) := by
  have hk := H.length_eq
  induction n generalizing l with
  | zero => exact Weak.inWindow p hn hi hl hr
  | succ n ih =>
    obtain ⟨q, hq, prev, last⟩ := (transfer_le_iff (p.bounded hl)).mp hr
    have linked := ih (by omega) (by omega : d+q < k) prev
    have finish := Weak.inWindow (d := d) p hn (by omega : q < k) hl last
    have join : d*(s+n)+(d+q) = d*(s+(n+1))+q := by
      rw [← Nat.add_assoc s n 1, Nat.mul_succ, Nat.add_assoc]
    rw [join] at linked
    exact linked.trans finish

private theorem goLeft {j s i} (hi : i < k) (hs : s < j) (n : Nat) (hn : n ≤ s)
    {l} (hl : l < k) (hr : steps (backward p m d) n (p.rank i) ≤ p.rank l) :
    Weak p d j (d*s+i) (d*(s-n)+l) := by
  have hk := H.length_eq
  induction n generalizing l with
  | zero => exact Weak.inWindow p hs hi hl hr
  | succ n ih =>
    obtain ⟨q, hq, prev, last⟩ := (transfer_le_iff (p.bounded hl)).mp hr
    have linked := ih (by omega) (by omega : q < k) prev
    have finish := Weak.inWindow (d := d) p (by omega : s-(n+1) < j) (by omega : d+q < k) hl last
    have eq : s-n = (s-(n+1))+1 := by omega
    rw [eq, Nat.mul_succ, Nat.add_assoc] at linked
    exact linked.trans finish

/-- Exact comparison using a pair of fixed rank maps, independently of stack length. -/
theorem weak_iff_threshold {j s t i l} (hs : s < j) (ht : t < j) (hi : i < k) (hl : l < k) :
    Weak p d j (d*s+i) (d*t+l) ↔ threshold p m d s (p.rank i) t ≤ p.rank l := by
  refine ⟨H.necessary hi hl, ?_⟩
  intro h
  by_cases hst : s ≤ t
  · simp only [threshold, ite_eq_left hst] at h
    have eq : s+(t-s) = t := by omega
    simpa only [eq] using H.goRight hi (t-s) (by omega : s+(t-s)<j) hl h
  · simp only [threshold, ite_eq_right hst] at h
    have eq : s-(s-t) = t := by omega
    simpa only [eq] using H.goLeft hi hs (s-t) (by omega) hl h

/-- Compatibility makes the physical-window relation a strict partial order. -/
theorem strict_asymmetric {j a b} (h : Below p d j a b) : ¬ Weak p d j b a := by
  induction h with
  | window t i l ht hi hl hr =>
    intro reverse
    have impossible := (H.weak_iff_threshold ht ht hl hi).mp reverse
    simp [threshold, steps] at impossible
    omega
  | trans _ hyz ih _ =>
    exact fun reverse => ih (Weak.trans (Or.inr hyz) reverse)

end Compatible
end SolvedMath.PatternSeparator
