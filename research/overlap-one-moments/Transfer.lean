import Init

/-! The mixed-difference transfer induced by the overlap-one endpoint recurrence.
This research module concerns the return representation and its total-minor
obstruction. It does not postulate a measure or a Stieltjes property. -/

namespace OverlapOne

def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _+1 => 0
  | n+1, k+1 => choose n k + choose n (k+1)

def sumInt (n : Nat) (f : Nat → Int) : Int :=
  match n with
  | 0 => 0
  | k+1 => sumInt k f + f k

def difference (f : Nat → Int) : Nat → Nat → Int
  | 0, x => f x
  | n+1, x => difference f n (x+1) - difference f n x

abbrev State := Nat × Nat

def weight (a b c x y v : Nat) : Int :=
  (choose (x+2*a+c) a * choose (v+c-1) (c-1) * choose (y+2*b-v) b : Nat)

def transfer (a b c : Nat) (f : State → Int) (s : State) : Int :=
  sumInt (s.2+b+1) (fun v =>
    weight a b c s.1 s.2 v * f (s.1+a+c+v, s.2+b-v))

def basis (u s : State) : Int :=
  (choose s.1 u.1 * choose s.2 u.2 : Nat)

def coefficient (f : State → Int) (u : State) : Int :=
  difference (fun x => difference (fun y => f (x,y)) u.2 0) u.1 0

def matrix (a b c : Nat) (u v : State) : Int :=
  coefficient (transfer a b c (basis u)) v

def minor (m : State → State → Int) (u₁ u₂ v₁ v₂ : State) : Int :=
  m u₁ v₁ * m u₂ v₂ - m u₁ v₂ * m u₂ v₁

def oppositePairs : Prop :=
  minor (matrix 1 1 3) (0,0) (1,1) (0,2) (2,0) = 200 ∧
  minor (matrix 1 1 3) (0,2) (2,0) (0,0) (1,1) = -630

theorem exact_minors : oppositePairs := by
  unfold oppositePairs
  decide +kernel

theorem minor_swap_rows (m : State → State → Int) (x y u v : State) :
    minor m y x u v = -(minor m x y u v) := by
  simp only [minor, Int.neg_sub, Int.mul_comm]

theorem minor_swap_cols (m : State → State → Int) (x y u v : State) :
    minor m x y v u = -(minor m x y u v) := by
  simp only [minor, Int.neg_sub]

/-- Every numerical labeling of the states with distinct labels leaves a
negative increasing two-by-two minor in this transfer matrix. -/
theorem no_total_nonnegative_order (key : State → Nat)
    (distinct : ∀ u v, key u = key v → u = v) :
    ∃ x y u v, key x < key y ∧ key u < key v ∧ minor (matrix 1 1 3) x y u v < 0 := by
  let A : State := (0,0)
  let B : State := (1,1)
  let C : State := (0,2)
  let D : State := (2,0)
  have ab : key A ≠ key B := fun h => (by decide : A ≠ B) (distinct _ _ h)
  have cd : key C ≠ key D := fun h => (by decide : C ≠ D) (distinct _ _ h)
  have first : minor (matrix 1 1 3) A B C D = 200 := exact_minors.1
  have second : minor (matrix 1 1 3) C D A B = -630 := exact_minors.2
  by_cases h : key A < key B
  · by_cases k : key C < key D
    · exact ⟨C,D,A,B,k,h,by omega⟩
    · exact ⟨A,B,D,C,h,by omega,by rw [minor_swap_cols, first]; decide⟩
  · by_cases k : key C < key D
    · exact ⟨B,A,C,D,by omega,k,by rw [minor_swap_rows, first]; decide⟩
    · refine ⟨D,C,B,A,by omega,by omega,?_⟩
      rw [minor_swap_rows _ C D B A, minor_swap_cols _ C D A B, second]
      decide

end OverlapOne

namespace OverlapOne

theorem sum_congr {n : Nat} {f g : Nat → Int} (h : ∀ i < n, f i = g i) :
    sumInt n f = sumInt n g := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumInt, sumInt, ih (fun i hi => h i (by omega)), h n (by omega)]

theorem sum_zero (n : Nat) : sumInt n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumInt, ih]

theorem sum_add (n : Nat) (f g : Nat → Int) :
    sumInt n (fun i => f i + g i) = sumInt n f + sumInt n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumInt, ih]; omega

theorem sum_smul (n : Nat) (z : Int) (f : Nat → Int) :
    sumInt n (fun i => z * f i) = z * sumInt n f := by
  induction n with
  | zero => simp [sumInt]
  | succ n ih => simp only [sumInt, ih, Int.mul_add]

private theorem sum_indicator {n k : Nat} (hk : k < n) (f : Nat → Int) :
    sumInt n (fun i => if k = i then f i else 0) = f k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [sumInt]
    by_cases h : k = n
    · subst k
      have hzero : sumInt n (fun i => if n = i then f i else 0) = 0 :=
        (sum_congr (g := fun _ => 0) (fun i hi => ite_eq_right (by omega))).trans (sum_zero n)
      simp [hzero]
    · simp [h, ih (by omega)]

private def binApply : Nat → (Nat → Int) → Int
  | 0, f => f 0
  | n+1, f => binApply n f + binApply n (fun i => f (i+1))

private theorem bin_congr (n : Nat) {f g : Nat → Int} (h : ∀ i ≤ n, f i = g i) :
    binApply n f = binApply n g := by
  induction n generalizing f g with
  | zero => exact h _ (by omega)
  | succ n ih =>
    rw [binApply, binApply, ih (f := f) (g := g) (fun i hi => h i (by omega))]
    exact congrArg _ (ih (fun i hi => h (i+1) (by omega)))

private theorem bin_sub (n : Nat) (f g : Nat → Int) :
    binApply n (fun i => f i-g i) = binApply n f - binApply n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [binApply, ih]; omega

private theorem bin_zero (n : Nat) : binApply n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [binApply, ih]

private theorem bin_sum (n k : Nat) (f : Nat → Nat → Int) :
    binApply n (fun i => sumInt k (fun j => f i j)) = sumInt k (fun j => binApply n (fun i => f i j)) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [binApply, ih, ih, ← sum_add]
    rfl

private theorem bin_scale (n : Nat) (a : Int) (f : Nat → Int) :
    binApply n (fun i => f i * a) = binApply n f * a := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [binApply, ih, Int.add_mul]

private theorem bin_indicator (n k : Nat) :
    binApply n (fun i => if i = k then 1 else 0) = (choose n k : Int) := by
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih =>
    rw [binApply, ih]
    cases k with
    | zero => simp [bin_zero, choose]
    | succ k =>
      change _ + binApply n (fun i => if i+1 = k+1 then 1 else 0) = _
      simp only [Nat.add_right_cancel_iff, ih, choose, Int.natCast_add]
      omega

private theorem bin_coefficients (n cut : Nat) (hn : n ≤ cut) (f : Nat → Int) :
    binApply n f = sumInt (cut+1) (fun p => (choose n p : Int) * f p) := by
  calc
    _ = binApply n (fun i => sumInt (cut+1) (fun p => (if i = p then 1 else 0) * f p)) := by
      apply bin_congr
      intro i hi
      calc
        f i = sumInt (cut+1) (fun p => if i = p then f p else 0) := (sum_indicator (by omega) f).symm
        _ = _ := by
          apply sum_congr
          intro p _
          by_cases h : i = p <;> simp [h]
    _ = _ := by rw [bin_sum]; simp only [bin_scale, bin_indicator]

private theorem newton (n x : Nat) (f : Nat → Int) :
    binApply n (fun i => difference f i x) = f (x+n) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [binApply, ih]
    change _ + binApply n (fun i => difference f i (x+1) - difference f i x) = _
    rw [bin_sub, ih, ih, show x+1+n = x+(n+1) by omega]
    omega

private theorem diff_bin (n x t : Nat) (f : Nat → Nat → Int) :
    difference (fun i => binApply t (f i)) n x =
    binApply t (fun k => difference (fun i => f i k) n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp only [difference, ih, bin_sub]

/-- Finite Newton interpolation uses exactly the mixed differences defining the matrix. -/
theorem interpolate (f : State → Int) (cut x y : Nat) (hx : x ≤ cut) (hy : y ≤ cut) :
    f (x,y) = sumInt (cut+1) (fun p => sumInt (cut+1) (fun q => coefficient f (p,q) * basis (p,q) (x,y))) := by
  have pair : binApply x (fun p => binApply y (fun q => coefficient f (p,q))) = f (x,y) := by
    have point (z : Nat) : binApply y (fun q => difference (fun u => f (z,u)) q 0) = f (z,y) := by
      simpa using newton y 0 (fun u => f (z,u))
    have row (p : Nat) : binApply y (fun q => coefficient f (p,q)) = difference (fun u => f (u,y)) p 0 := by
      unfold coefficient
      rw [← diff_bin]
      simp only [point]
    simp only [row]
    simpa using newton x 0 (fun u => f (u,y))
  rw [← pair, bin_coefficients x cut hx]
  apply sum_congr
  intro p _
  rw [bin_coefficients y cut hy, ← sum_smul]
  apply sum_congr
  intro q _
  simp only [basis, Int.natCast_mul]
  ac_rfl

end OverlapOne

namespace OverlapOne

private theorem sum_swap (n m : Nat) (f : Nat → Nat → Int) :
    sumInt n (fun i => sumInt m (f i)) = sumInt m (fun j => sumInt n (fun i => f i j)) := by
  induction n with
  | zero => simp only [sumInt, sum_zero]
  | succ n ih => rw [sumInt, ih, ← sum_add]; rfl

private theorem transfer_sum (a b c n : Nat) (f : Nat → State → Int) (s : State) :
    transfer a b c (fun t => sumInt n (fun i => f i t)) s =
    sumInt n (fun i => transfer a b c (f i) s) := by
  unfold transfer
  simp only [← sum_smul]
  exact sum_swap ..

private theorem transfer_scale (a b c : Nat) (z : Int) (f : State → Int) (s : State) :
    transfer a b c (fun t => z * f t) s = z * transfer a b c f s := by
  unfold transfer
  rw [← sum_smul]
  apply sum_congr
  intro v _
  dsimp only
  ac_rfl

def walk (a b c : Nat) : Nat → (State → Int) → State → Int
  | 0, f, s => f s
  | r+1, f, s => transfer a b c (walk a b c r f) s

private theorem walk_congr (a b c n : Nat) (s : State) (f g : State → Int)
    (h : ∀ t : State, t.1+t.2 ≤ s.1+s.2+n*(a+b+c) → f t = g t) :
    walk a b c n f s = walk a b c n g s := by
  induction n generalizing s with
  | zero => exact h s (by omega)
  | succ n ih =>
    apply sum_congr
    intro v hv
    apply congrArg (_ * ·)
    apply ih
    intro t ht
    apply h t
    rw [Nat.succ_mul]
    dsimp at ht
    omega

private theorem walk_sum (a b c r n : Nat) (f : Nat → State → Int) (s : State) :
    walk a b c r (fun t => sumInt n (fun i => f i t)) s = sumInt n (fun i => walk a b c r (f i) s) := by
  induction r generalizing s with
  | zero => rfl
  | succ r ih => simp only [walk, funext ih, transfer_sum]

private theorem walk_scale (a b c r : Nat) (z : Int) (f : State → Int) (s : State) :
    walk a b c r (fun t => z * f t) s = z * walk a b c r f s := by
  induction r generalizing s with
  | zero => rfl
  | succ r ih => simp only [walk, funext ih, transfer_scale]

private theorem walk_last (a b c r : Nat) (f : State → Int) (s : State) :
    walk a b c (r+1) f s = walk a b c r (transfer a b c f) s := by
  induction r generalizing s with
  | zero => rfl
  | succ r ih => change transfer _ _ _ (walk _ _ _ (r+1) f) s = _; rw [funext ih]; rfl

/-- Matrix powers applied to the delta function at zero. A return in r more
steps is possible only within the rectangle of side r*(a+b+c). -/
def matrixPowerAtZero (a b c : Nat) : Nat → State → Int
  | 0, u => if u = (0,0) then 1 else 0
  | r+1, u =>
    let n := r*(a+b+c)+1
    sumInt n (fun i => sumInt n (fun k => matrix a b c u (i,k) * matrixPowerAtZero a b c r (i,k)))

theorem walk_basis_eq_matrix (a b c r : Nat) (u : State) :
    walk a b c r (basis u) (0,0) = matrixPowerAtZero a b c r u := by
  induction r generalizing u with
  | zero =>
    rcases u with ⟨p,q⟩
    cases p <;> cases q <;> simp [matrixPowerAtZero, walk, basis, choose]
  | succ r ih =>
    let cut := r*(a+b+c)
    let f := transfer a b c (basis u)
    let g : State → Int := fun t => sumInt (cut+1) (fun p => sumInt (cut+1)
      (fun q => matrix a b c u (p,q) * basis (p,q) t))
    have eq : walk a b c r f (0,0) = walk a b c r g (0,0) := by
      apply walk_congr
      intro t ht
      simp only [Nat.zero_add] at ht
      exact interpolate f cut t.1 t.2 (by dsimp [cut]; omega) (by dsimp [cut]; omega)
    rw [walk_last, eq]
    simp only [g, walk_sum, walk_scale, ih, matrixPowerAtZero, cut]

/-- The raw endpoint counts beginning at one window are exactly the (0,0)
return entries, with the first-window shift already incorporated. -/
theorem endpointCount_eq_return (a b c r : Nat) :
    walk a b c r (fun _ => 1) (0,0) = matrixPowerAtZero a b c r (0,0) := by
  have eq : basis (0,0) = (fun _ => 1) := by funext t; simp [basis, choose]
  rw [← eq]
  exact walk_basis_eq_matrix a b c r (0,0)

end OverlapOne

namespace OverlapOne

private inductive Axis | lower | upper

private def bump : Axis → State → State
  | .lower, (x,y) => (x+1,y)
  | .upper, (x,y) => (x,y+1)

private theorem bumps_commute (d e : Axis) (s : State) : bump d (bump e s) = bump e (bump d s) := by
  cases d <;> cases e <;> rfl

private def delta (d : Axis) (f : State → Int) (s : State) : Int := f (bump d s) - f s

private def differences : List Axis → (State → Int) → State → Int
  | [], f, s => f s
  | d::rest, f, s => differences rest (delta d f) s

private def Absolute (f : State → Int) : Prop := ∀ dirs s, 0 ≤ differences dirs f s

private theorem delta_const (d : Axis) (z : Int) : delta d (fun _ => z) = fun _ => 0 := by
  funext s
  simp [delta]

private theorem diff_zero (dirs : List Axis) (s : State) :
    differences dirs (fun _ => 0) s = 0 := by
  induction dirs with
  | nil => rfl
  | cons d rest ih => simpa only [differences, delta_const] using ih

private theorem abs_const (z : Int) (hz : 0 ≤ z) : Absolute (fun _ => z) := by
  intro ds s
  cases ds with
  | nil => exact hz
  | cons d rest => simp [differences, delta_const, diff_zero]

private theorem diff_add (dirs : List Axis) (f g : State → Int) (s : State) :
    differences dirs (fun t => f t + g t) s = differences dirs f s + differences dirs g s := by
  induction dirs generalizing f g with
  | nil => rfl
  | cons d rest ih =>
    have split : delta d (fun t => f t+g t) = fun t => delta d f t+delta d g t := by
      funext t; dsimp only [delta]; omega
    simp only [differences, split, ih]

private theorem diff_shift (dirs : List Axis) (d : Axis) (f : State → Int) (s : State) :
    differences dirs (fun t => f (bump d t)) s = differences dirs f (bump d s) := by
  induction dirs generalizing f with
  | nil => rfl
  | cons e rest ih =>
    have step : delta e (fun t => f (bump d t)) = fun t => delta e f (bump d t) := by
      funext t; dsimp only [delta]; rw [bumps_commute d e]
    simp only [differences, step, ih]

private theorem Absolute.shift {f : State → Int} (h : Absolute f) (d : Axis) :
    Absolute (fun s => f (bump d s)) := by
  intro ds s
  rw [diff_shift]
  exact h _ _

private theorem Absolute.deriv {f : State → Int} (h : Absolute f) (d : Axis) :
    Absolute (delta d f) := fun ds s => h (d::ds) s

private theorem abs_mul {f g : State → Int} (hf : Absolute f) (hg : Absolute g) :
    Absolute (fun s => f s*g s) := by
  intro ds s
  induction ds generalizing f g with
  | nil => exact Int.mul_nonneg (hf [] s) (hg [] s)
  | cons d rest ih =>
    have rule : delta d (fun t => f t * g t) =
        fun t => delta d f t * g (bump d t) + f t * delta d g t := by
      funext t
      simp only [delta, Int.mul_sub, Int.sub_mul]
      omega
    rw [differences, rule, diff_add]
    exact Int.add_nonneg (ih (hf.deriv d) (hg.shift d)) (ih hf (hg.deriv d))

private theorem abs_choose (L : State → Nat) (k : Nat)
    (moves : ∀ d, (∀ s, L (bump d s) = L s) ∨ (∀ s, L (bump d s) = L s+1)) :
    Absolute (fun s => (choose (L s) k : Int)) := by
  intro ds s
  induction ds generalizing k with
  | nil => exact Int.natCast_nonneg _
  | cons d rest ih =>
    rw [differences]
    rcases moves d with same | inc
    · have h : delta d (fun t => (choose (L t) k : Int)) = fun _ => 0 := by
        funext t; simp [delta, same]
      simp [h, diff_zero]
    · cases k with
      | zero => simp [delta_const, choose, diff_zero]
      | succ k =>
        have h : delta d (fun t => (choose (L t) (k+1) : Int)) =
            fun t => (choose (L t) k : Int) := by
          funext t; simp [delta, inc, choose]
        exact h ▸ ih k

private def convolution (f : State → Int) (g : Nat → Int) (s : State) : Int :=
  sumInt (s.2+1) (fun v => f (s.1,v) * g (s.2-v))

private theorem sum_sub (n : Nat) (f g : Nat → Int) :
    sumInt n (fun i => f i-g i) = sumInt n f - sumInt n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumInt, ih]; omega

private theorem conv_lower (f : State → Int) (g : Nat → Int) :
    delta .lower (convolution f g) = convolution (delta .lower f) g := by
  funext ⟨x,y⟩
  simp only [delta, convolution, bump, Int.sub_mul, sum_sub]

private theorem conv_upper (f : State → Int) (g : Nat → Int) :
    delta .upper (convolution f g) = fun s =>
      convolution f (fun w => g (w+1)-g w) s + f (bump .upper s)*g 0 := by
  funext ⟨x,y⟩
  simp only [delta, convolution, bump]
  rw [sumInt]
  simp only [Nat.sub_self, Int.mul_sub, sum_sub]
  have h : sumInt (y+1) (fun v => f (x,v) * g (y+1-v)) =
      sumInt (y+1) (fun v => f (x,v) * g (y-v+1)) := by
    apply sum_congr
    intro v hv
    rw [show y+1-v = y-v+1 by omega]
  rw [h]
  omega

private theorem abs_convolution {f : State → Int} {g : Nat → Int}
    (hf : Absolute f) (hg : Absolute (fun s => g s.2)) : Absolute (convolution f g) := by
  intro ds s
  induction ds generalizing f g with
  | nil =>
    change 0 ≤ sumInt (s.2+1) _
    have nonneg (n : Nat) (v : Nat → Int) (hv : ∀ i, 0 ≤ v i) : 0 ≤ sumInt n v := by
      induction n with
      | zero => exact Int.le_refl 0
      | succ n ih => exact Int.add_nonneg ih (hv n)
    exact nonneg _ _ (fun v => Int.mul_nonneg (hf [] (s.1,v)) (hg [] (0,s.2-v)))
  | cons d rest ih =>
    rw [differences]
    cases d with
    | lower =>
      rw [conv_lower]; exact ih (hf.deriv .lower) hg
    | upper =>
      rw [conv_upper, diff_add]
      exact Int.add_nonneg (ih hf (hg.deriv .upper))
        (abs_mul (hf.shift .upper) (abs_const _ (hg [] (0,0))) rest s)

private theorem Absolute.translateUpper {f : State → Int} (hf : Absolute f) (b : Nat) :
    Absolute (fun s => f (s.1,s.2+b)) := by
  induction b with
  | zero => exact hf
  | succ b ih =>
    have h := ih.shift .upper
    simpa only [bump, Nat.succ_add, Nat.add_succ] using h

private theorem abs_transfer_basis (a b c p q : Nat) (hc : 0 < c) :
    Absolute (transfer a b c (basis (p,q))) := by
  let f : State → Int := fun s =>
    (choose (s.1+2*a+c) a : Int) * (choose (s.1+a+c+s.2) p : Int) * (choose (s.2+(c-1)) (c-1) : Int)
  let g : Nat → Int := fun w => (choose (w+b) b : Int) * (choose w q : Int)
  have hf : Absolute f := by
    apply abs_mul
    · apply abs_mul
      · apply abs_choose; intro d; cases d with
        | lower => right; intro s; simp [bump]; omega
        | upper => left; intro s; rfl
      · apply abs_choose; intro d; right; intro s; cases d <;> simp [bump] <;> omega
    · apply abs_choose; intro d; cases d with
      | lower => left; intro s; rfl
      | upper => right; intro s; simp [bump]; omega
  have hg : Absolute (fun s => g s.2) := by
    apply abs_mul
    · apply abs_choose; intro d; cases d with
      | lower => left; intro s; rfl
      | upper => right; intro s; simp [bump]; omega
    · apply abs_choose; intro d; cases d with
      | lower => left; intro s; rfl
      | upper => right; intro s; rfl
  have eq : transfer a b c (basis (p,q)) = fun s => convolution f g (s.1,s.2+b) := by
    funext ⟨x,y⟩
    apply sum_congr
    intro v hv
    simp only [weight, basis, f, g, Int.natCast_mul]
    rw [show v+c-1 = v+(c-1) by omega, show y+2*b-v = y+b-v+b by omega]
    ac_rfl
  rw [eq]
  exact (abs_convolution hf hg).translateUpper b

private theorem Absolute.xdiff {f : State → Int} (hf : Absolute f) (n : Nat) :
    Absolute (fun s => difference (fun x => f (x,s.2)) n s.1) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.deriv .lower

private theorem Absolute.ydiff {f : State → Int} (hf : Absolute f) (n : Nat) :
    Absolute (fun s => difference (fun y => f (s.1,y)) n s.2) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.deriv .upper

/-- Every entry of the time-independent return matrix is nonnegative. -/
theorem matrix_nonnegative (a b c : Nat) (hc : 0 < c) (u v : State) : 0 ≤ matrix a b c u v :=
  (((abs_transfer_basis a b c u.1 u.2 hc).ydiff v.2).xdiff v.1) [] (0,0)

end OverlapOne

/-- info: 'OverlapOne.endpointCount_eq_return' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OverlapOne.endpointCount_eq_return

/-- info: 'OverlapOne.matrix_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OverlapOne.matrix_nonnegative

/-- info: 'OverlapOne.no_total_nonnegative_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms OverlapOne.no_total_nonnegative_order
