module

public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace FoldedLinearForests

open Set
open scoped BigOperators

/-- Every finite block reappears in every sufficiently long factor. -/
def AlmostPeriodic {A : Type} (w : ℕ → A) : Prop :=
  ∀ start len, ∃ R, ∀ off, ∃ pos, off ≤ pos ∧ pos + len ≤ off + R ∧
    ∀ j < len, w (pos + j) = w (start + j)

noncomputable def letter (a : ℝ) (i : ℕ) : Bool :=
  decide (⌊(i : ℝ) * a⌋ < ⌊((i : ℝ) + 1) * a⌋)

theorem letter_difference {a : ℝ} (ha : 0 < a) (hb : a < 1) (i : ℕ) :
    (if letter a i then (1 : ℤ) else 0) = ⌊((i : ℝ) + 1) * a⌋ - ⌊(i : ℝ) * a⌋ := by
  have h₁ : ⌊(i : ℝ) * a⌋ ≤ ⌊((i : ℝ) + 1) * a⌋ :=
    Int.floor_mono (by linarith [show ((i : ℝ) + 1) * a = i*a + a by ring])
  have h₂ : ((i : ℝ) + 1) * a < ↑⌊(i : ℝ) * a⌋ + 2 := by
    rw [add_mul, one_mul]
    linarith [Int.lt_floor_add_one ((i : ℝ) * a)]
  have h₃ : ⌊((i : ℝ) + 1) * a⌋ < ⌊(i : ℝ) * a⌋ + 2 := by
    exact Int.floor_lt.mpr (by push_cast; exact h₂)
  unfold letter
  split <;> simp_all <;> omega

theorem block_count {a : ℝ} (ha : 0 < a) (hb : a < 1) (s n : ℕ) :
    ∑ j ∈ Finset.range n, (if letter a (s+j) then (1 : ℤ) else 0) =
      ⌊((s+n : ℕ) : ℝ) * a⌋ - ⌊(s : ℝ) * a⌋ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, letter_difference ha hb]
    simp only [Nat.add_succ, Nat.cast_succ]
    omega

theorem block_discrepancy {a : ℝ} (ha : 0 < a) (hb : a < 1) (s n : ℕ) :
    |(↑(∑ j ∈ Finset.range n, (if letter a (s+j) then (1 : ℤ) else 0)) : ℝ) - n*a| < 1 := by
  rw [block_count ha hb, Int.cast_sub, abs_lt]
  have hu := Int.lt_floor_add_one (((s+n : ℕ) : ℝ) * a)
  have hl := Int.floor_le (((s+n : ℕ) : ℝ) * a)
  push_cast at hu hl ⊢
  rw [add_mul] at hu hl ⊢
  constructor <;> linarith [Int.lt_floor_add_one ((s : ℝ) * a), Int.floor_le ((s : ℝ) * a)]

private theorem orbit_pair {a lo hi : ℝ} (ha : Irrational a) (hlt : lo < hi) (x : ℝ) :
    ∃ z q : ℤ, lo < x + (z : ℝ)*a + q ∧ x + (z : ℝ)*a + q < hi := by
  have hd : Dense (AddSubgroup.closure ({a, 1} : Set ℝ) : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr (by simpa using ha)
  obtain ⟨v,hv,hw⟩ := hd.exists_mem_open isOpen_Ioo
    (nonempty_Ioo.mpr (show lo - x < hi - x by linarith))
  obtain ⟨z,q,he⟩ := AddSubgroup.mem_closure_pair.mp hv
  simp only [zsmul_eq_mul, mul_one] at he
  exact ⟨z,q,by linarith [hw.1],by linarith [hw.2]⟩

/-- Every sufficiently long interval of natural-number iterates hits the specified open phases. -/
theorem bounded_phase_hits {a lo hi : ℝ} (ha : Irrational a) (hl : 0 ≤ lo)
    (hh : hi ≤ 1) (hlt : lo < hi) :
    ∃ B : ℕ, ∀ off : ℕ, ∃ pos, off ≤ pos ∧ pos ≤ off+B ∧
      lo < Int.fract ((pos : ℝ)*a) ∧ Int.fract ((pos : ℝ)*a) < hi := by
  classical
  let U (i : ℤ × ℤ) : Set ℝ := Ioo (lo - (i.1 : ℝ)*a - i.2) (hi - (i.1 : ℝ)*a - i.2)
  have cov : Icc (0 : ℝ) 1 ⊆ ⋃ i, U i := by
    intro x _
    obtain ⟨z,q,hz,hq⟩ := orbit_pair ha hlt x
    exact mem_iUnion.mpr ⟨(z,q), show x ∈ U (z,q) from ⟨by dsimp; linarith,by dsimp; linarith⟩⟩
  obtain ⟨F,hF⟩ := isCompact_Icc.elim_finite_subcover U (fun _ => isOpen_Ioo) cov
  let M := ∑ i ∈ F, i.1.natAbs
  refine ⟨2*M,?_⟩
  intro off
  let k := off + M
  let x := Int.fract ((k : ℝ)*a)
  have hx : x ∈ Icc (0 : ℝ) 1 := ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  obtain ⟨i,hiF,hiU⟩ := mem_iUnion₂.mp (hF hx)
  have hm : i.1.natAbs ≤ M := Finset.single_le_sum (fun j _ => Nat.zero_le j.1.natAbs) hiF
  have abs₁ := Int.le_natAbs (a := i.1)
  have abs₂ := Int.le_natAbs (a := -i.1)
  simp only [Int.natAbs_neg] at abs₂
  let pos := ((k : ℤ) + i.1).toNat
  have hp : (pos : ℤ) = (k : ℤ) + i.1 := by
    dsimp [pos,k]; omega
  have hp' : (pos : ℝ) = (k : ℝ) + (i.1 : ℝ) := by exact_mod_cast hp
  have hxlo : lo < x + (i.1 : ℝ)*a + i.2 := by linarith [hiU.1]
  have hxhi : x + (i.1 : ℝ)*a + i.2 < hi := by linarith [hiU.2]
  have eqf : Int.fract ((pos : ℝ)*a) = x + (i.1 : ℝ)*a + i.2 := by
    let u := x + (i.1 : ℝ)*a + i.2
    have heq : (pos : ℝ)*a = u + ((⌊(k : ℝ)*a⌋ - i.2 : ℤ) : ℝ) := by
      dsimp only [u,x,Int.fract]; rw [hp']; push_cast; ring
    rw [heq, Int.fract_add_intCast]
    exact Int.fract_eq_self.mpr ⟨by dsimp only [u]; linarith,by dsimp [u]; linarith⟩
  refine ⟨pos, ?_, ?_, eqf ▸ hxlo, eqf ▸ hxhi⟩ <;> dsimp [k] at hp <;> omega

private theorem finite_floor_window (y : ℕ → ℝ) (n : ℕ) :
    ∃ e : ℝ, 0 < e ∧ ∀ j ≤ n, ∀ t : ℝ, 0 ≤ t → t < e → ⌊y j + t⌋ = ⌊y j⌋ := by
  have one (j : ℕ) : ∃ e : ℝ, 0 < e ∧
      ∀ t : ℝ, 0 ≤ t → t < e → ⌊y j + t⌋ = ⌊y j⌋ := by
    refine ⟨↑⌊y j⌋ + 1 - y j,by linarith [Int.lt_floor_add_one (y j)],?_⟩
    intro t ht hte
    apply Int.floor_eq_iff.mpr
    constructor <;> linarith [Int.floor_le (y j)]
  induction n with
  | zero =>
    obtain ⟨e,he,h⟩ := one 0
    exact ⟨e,he,fun j hj => (Nat.eq_zero_of_le_zero hj) ▸ h⟩
  | succ n ih =>
    obtain ⟨e,he,h⟩ := ih
    obtain ⟨d,hd,h'⟩ := one (n+1)
    refine ⟨min e d,lt_min he hd,?_⟩
    intro j hj t ht ht'
    by_cases hj' : j ≤ n
    · exact h j hj' t ht ((lt_min_iff.mp ht').1)
    · have eq : j = n+1 := by omega
      exact eq ▸ h' t ht ((lt_min_iff.mp ht').2)

theorem mechanical_almostPeriodic {a : ℝ} (ha : Irrational a) : AlmostPeriodic (letter a) := by
  intro s n
  let y (j : ℕ) := ((s+j : ℕ) : ℝ)*a
  obtain ⟨e,he,stable⟩ := finite_floor_window y n
  let t := Int.fract ((s : ℝ)*a)
  have ht : t < 1 := Int.fract_lt_one _
  obtain ⟨B,hB⟩ := bounded_phase_hits ha (Int.fract_nonneg _) (min_le_left 1 (t+e))
    (show t < min 1 (t+e) from lt_min ht (by linarith))
  refine ⟨B+n,?_⟩
  intro off
  obtain ⟨pos,hp,hpB,hlo,hhi⟩ := hB off
  let delta := Int.fract ((pos : ℝ)*a) - t
  have hd : 0 ≤ delta := sub_nonneg.mpr hlo.le
  have hde : delta < e := by
    dsimp [delta]; linarith [(lt_min_iff.mp hhi).2]
  let c := ⌊(pos : ℝ)*a⌋ - ⌊(s : ℝ)*a⌋
  have hf (j : ℕ) (hj : j ≤ n) :
      ⌊((pos+j : ℕ) : ℝ)*a⌋ = ⌊((s+j : ℕ) : ℝ)*a⌋ + c := by
    have ar : ((pos+j : ℕ) : ℝ)*a = (y j + delta) + (c : ℝ) := by
      dsimp only [y,delta,t,c,Int.fract]
      push_cast; ring
    rw [ar, Int.floor_add_intCast, stable j hj delta hd hde]
  refine ⟨pos,hp,by omega,?_⟩
  intro j hj
  have h₁ := hf j (by omega)
  have h₂ := hf (j+1) (by omega)
  simp only [Nat.add_succ, Nat.cast_succ] at h₂
  unfold letter
  simp only [h₁,h₂,add_lt_add_iff_right]

end FoldedLinearForests
