import SolvedMath.PatternReachability

namespace SolvedMath.PatternSeparator

private theorem steps_add (f : Nat → Nat) (n q r : Nat) :
    steps f (n+q) r = steps f q (steps f n r) := by
  induction q with
  | zero => rfl
  | succ q ih => exact congrArg f ih

private theorem steps_fixed {f : Nat → Nat} {r : Nat} (h : f r = r) (n : Nat) :
    steps f n r = r := by
  induction n with
  | zero => rfl
  | succ n ih => exact (congrArg f ih).trans h

private theorem steps_direction {f : Nat → Nat} {r : Nat}
    (hm : ∀ {x y}, x ≤ y → f x ≤ f y) (n : Nat) :
    (r ≤ f r → steps f n r ≤ steps f (n+1) r) ∧
    (f r ≤ r → steps f (n+1) r ≤ steps f n r) := by
  induction n with
  | zero => exact ⟨id, id⟩
  | succ n ih => exact ⟨fun h => hm (ih.1 h), fun h => hm (ih.2 h)⟩

private theorem steps_progress {f : Nat → Nat} {r : Nat}
    (hm : ∀ {x y}, x ≤ y → f x ≤ f y) (n : Nat)
    (h : steps f n r ≠ steps f (n+1) r) :
    (r ≤ f r → r+(n+1) ≤ steps f (n+1) r) ∧
    (f r ≤ r → steps f (n+1) r+(n+1) ≤ r) := by
  have dir := steps_direction hm n (r := r)
  induction n with
  | zero =>
    change r ≠ f r at h
    change (r ≤ f r → r+1 ≤ f r) ∧ (f r ≤ r → f r+1 ≤ r)
    omega
  | succ n ih =>
    have prev : steps f n r ≠ steps f (n+1) r :=
      fun he => h (congrArg f he)
    have bounds := ih prev (steps_direction hm n)
    constructor
    · intro inc
      have := bounds.1 inc
      have := dir.1 inc
      omega
    · intro dec
      have := bounds.2 dec
      have := dir.2 dec
      omega

/-- Iteration of an order-preserving self-map of the chain 0,...,k stabilizes
after at most k applications, uniformly in its starting point. -/
theorem steps_cap {f : Nat → Nat} {k r : Nat} (hr : r ≤ k)
    (hm : ∀ {x y}, x ≤ y → f x ≤ f y) (hb : ∀ x, f x ≤ k) (n : Nat) :
    steps f n r = steps f (min k n) r := by
  by_cases h : n ≤ k
  · rw [Nat.min_eq_right h]
  have hk : k ≤ n := by omega
  have fixed : f (steps f k r) = steps f k r := by
    by_cases he : steps f k r = steps f (k+1) r
    · exact he.symm
    · have bounds := steps_progress hm k he
      have upper : steps f (k+1) r ≤ k := hb _
      rcases Nat.le_total r (f r) with inc | dec
      · have := bounds.1 inc
        omega
      · have := bounds.2 dec
        omega
  obtain ⟨q, eq⟩ := Nat.exists_eq_add_of_le hk
  calc
    _ = steps f (k+q) r := congrArg (fun n => steps f n r) eq
    _ = steps f k r := (steps_add f k q r).trans (steps_fixed fixed q)
    _ = _ := by rw [Nat.min_eq_left hk]

/-- The two oriented window distances have the same values after capping. -/
structure SameGap (k a b a' b' : Nat) : Prop where
  right : min k (b-a) = min k (b'-a')
  left : min k (a-b) = min k (a'-b')

theorem SameGap.reverse {k a b a' b'} (h : SameGap k a b a' b') :
    SameGap k b a b' a' := ⟨h.left,h.right⟩

private theorem threshold_both {k} (p : Permutation k) (m d s r t : Nat) :
    threshold p m d s r t =
      steps (backward p m d) (s-t) (steps (forward p m d) (t-s) r) := by
  unfold threshold
  split
  · rw [show s-t = 0 by omega]; rfl
  · rw [show t-s = 0 by omega]; rfl

theorem threshold_congr {k} (p : Permutation k) (m d : Nat) {s t S T r : Nat}
    (hr : r ≤ k) (h : SameGap k s t S T) :
    threshold p m d s r t = threshold p m d S r T := by
  let F := forward p m d
  let B := backward p m d
  have fm : ∀ {x y}, x ≤ y → F x ≤ F y := fun h => transfer_mono h
  have bm : ∀ {x y}, x ≤ y → B x ≤ B y := fun h => transfer_mono h
  have fb : ∀ x, F x ≤ k := fun _ => transfer_bounded _
  have bb : ∀ x, B x ≤ k := fun _ => transfer_bounded _
  have hforward : steps F (t-s) r = steps F (T-S) r := by
    rw [steps_cap hr fm fb (t-s), h.right, ← steps_cap hr fm fb (T-S)]
  have bounded : steps F (T-S) r ≤ k := by
    cases T-S with
    | zero => exact hr
    | succ n => exact fb _
  rw [threshold_both, threshold_both]
  change steps B (s-t) (steps F (t-s) r) = steps B (S-T) (steps F (T-S) r)
  rw [hforward, steps_cap bounded bm bb (s-t), h.left, ← steps_cap bounded bm bb (S-T)]

/-- Space on the two sides of the distinguished row, enough to place two additional
rows while preserving all three capped distances. -/
structure ArmsFit (k j s J S : Nat) : Prop where
  left : min (2*k) s ≤ S
  right : min (2*k) (j-1-s) ≤ J-1-S

structure ThreeGaps (k s a b S A B : Nat) : Prop where
  sa : SameGap k s a S A
  sb : SameGap k s b S B
  ab : SameGap k a b A B

private theorem capped_add (k u v : Nat) :
    min k (min k u + min k v) = min k (u+v) := by omega

private theorem compressed_length {k u v n N : Nat}
    (h : u+v ≤ n) (fits : min (2*k) n ≤ N) : min k u + min k v ≤ N := by omega

private theorem fit_ordered {k j s J S a b : Nat}
    (hs : s < j) (hS : S < J) (ha : a < j) (hb : b < j) (hab : a ≤ b)
    (fit : ArmsFit k j s J S) :
    ∃ A < J, ∃ B < J, ThreeGaps k s a b S A B := by
  have left := fit.left
  have right := fit.right
  by_cases hsa : s ≤ a
  · let u := min k (a-s)
    let v := min k (b-a)
    have bound : u+v ≤ J-1-S := compressed_length (by omega : (a-s)+(b-a) ≤ j-1-s) right
    refine ⟨S+u, by omega, S+u+v, by omega, ?_⟩
    have sum := capped_add k (a-s) (b-a)
    constructor <;> constructor <;> dsimp [u,v] at * <;> omega
  by_cases hbs : b ≤ s
  · let u := min k (s-b)
    let v := min k (b-a)
    have bound : u+v ≤ S := compressed_length (by omega : (s-b)+(b-a) ≤ s) left
    refine ⟨S-u-v, by omega, S-u, by omega, ?_⟩
    have sum := capped_add k (s-b) (b-a)
    constructor <;> constructor <;> dsimp [u,v] at * <;> omega
  · let u := min k (s-a)
    let v := min k (b-s)
    have boundL : u ≤ S := by dsimp [u]; omega
    have boundR : v ≤ J-1-S := by dsimp [v]; omega
    refine ⟨S-u, by omega, S+v, by omega, ?_⟩
    have sum := capped_add k (s-a) (b-s)
    constructor <;> constructor <;> dsimp [u,v] at * <;> omega

theorem ArmsFit.match_two {k j s J S a b : Nat}
    (fit : ArmsFit k j s J S) (hs : s < j) (hS : S < J) (ha : a < j) (hb : b < j) :
    ∃ A < J, ∃ B < J, ThreeGaps k s a b S A B := by
  rcases Nat.le_total a b with h | h
  · exact fit_ordered hs hS ha hb h fit
  · obtain ⟨B,hB,A,hA,w⟩ := fit_ordered hs hS hb ha h fit
    exact ⟨A,hA,B,hB,⟨w.sb,w.sa,w.ab.reverse⟩⟩

/-- Every distinguished row in j windows has an equivalent distinguished row in
J windows if the two lengths agree when capped at 4k+1. -/
theorem match_center {k j J s : Nat} (hs : s < j) (h : min (4*k+1) j = min (4*k+1) J) :
    ∃ S < J, ArmsFit k j s J S ∧ ArmsFit k J S j s := by
  by_cases eq : j = J
  · subst J
    exact ⟨s,hs,⟨Nat.min_le_right ..,Nat.min_le_right ..⟩,
      ⟨Nat.min_le_right ..,Nat.min_le_right ..⟩⟩
  have hj : 4*k+1 ≤ j := by omega
  have hJ : 4*k+1 ≤ J := by omega
  by_cases a : s < 2*k
  · exact ⟨s,by omega,⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
  by_cases b : j-1-s < 2*k
  · exact ⟨J-1-(j-1-s),by omega,⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
  · exact ⟨2*k,by omega,⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩

end SolvedMath.PatternSeparator
