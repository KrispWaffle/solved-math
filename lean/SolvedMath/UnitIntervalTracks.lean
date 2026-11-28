module

public import SolvedMath.InducedMinorRows
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Data.Finset.Interval

@[expose] public section

namespace UnitIntervalMinors

open Set SimpleGraph
open InducedMinorBands (IsInducedMinor Model)

/-- Actual closed intervals on the real line, with intersection as graph adjacency. -/
def intervalGraph {V : Type} (left right : V → ℝ) : SimpleGraph V where
  Adj i j := i ≠ j ∧ (Icc (left i) (right i) ∩ Icc (left j) (right j)).Nonempty
  symm := ⟨fun _ _ h => ⟨h.1.symm, inter_comm _ _ ▸ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

abbrev unitGraph {V : Type} (start : V → ℝ) := intervalGraph start (fun i => start i + 1)

private theorem contains_connected {V : Type} (left right : V → ℝ) (B : Finset V)
    (a b : ℝ) (hab : a ≤ b)
    (hit : ∀ i ∈ B, (Icc a b ∩ Icc (left i) (right i)).Nonempty)
    (covers : ∀ x ∈ Icc a b, ∃ i ∈ B, x ∈ Icc (left i) (right i)) :
    ((intervalGraph left right).induce (B : Set V)).Connected := by
  classical
  let G := (intervalGraph left right).induce (B : Set V)
  obtain ⟨i, hi, _⟩ := covers a (left_mem_Icc.mpr hab)
  let root : (B : Set V) := ⟨i, hi⟩
  apply (connected_iff_exists_forall_reachable G).2
  refine ⟨root, ?_⟩
  intro j
  by_contra hj
  let good := B.filter fun k => ∃ hk : k ∈ B, G.Reachable root ⟨k,hk⟩
  let bad := B \ good
  let region (F : Finset V) := ⋃ k ∈ F, Icc (left k) (right k)
  have closed (F : Finset V) : IsClosed (region F) :=
    isClosed_biUnion_finset fun _ _ => isClosed_Icc
  have hroot : i ∈ good := Finset.mem_filter.mpr ⟨hi, hi, .refl _⟩
  have hbad : j.val ∈ bad := by simpa [bad, good, j.property] using hj
  have unionCover : Icc a b ⊆ region good ∪ region bad := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := covers x hx
    by_cases h : k ∈ good
    · exact Or.inl (mem_iUnion₂.mpr ⟨k,h,hkx⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨k,Finset.mem_sdiff.mpr ⟨hk,h⟩,hkx⟩)
  obtain ⟨x,hxs,hxi⟩ := hit i hi
  obtain ⟨y,hys,hyj⟩ := hit j.val j.property
  obtain ⟨z,_,hz₁,hz₂⟩ := isPreconnected_closed_iff.mp isPreconnected_Icc
    (region good) (region bad) (closed _) (closed _) unionCover
    ⟨x,hxs,mem_iUnion₂.mpr ⟨i,hroot,hxi⟩⟩ ⟨y,hys,mem_iUnion₂.mpr ⟨j.val,hbad,hyj⟩⟩
  obtain ⟨v,hv,hvz⟩ := mem_iUnion₂.mp hz₁
  obtain ⟨w,hw,hwz⟩ := mem_iUnion₂.mp hz₂
  obtain ⟨_, hvm, reach⟩ := Finset.mem_filter.mp hv
  obtain ⟨hwm, hng⟩ := Finset.mem_sdiff.mp hw
  have ne : v ≠ w := fun h => hng (h ▸ hv)
  have edge : G.Adj ⟨v,hvm⟩ ⟨w,hwm⟩ := ⟨ne,z,hvz,hwz⟩
  exact hng (Finset.mem_filter.mpr ⟨hwm,hwm,reach.trans edge.reachable⟩)

private theorem window_residue (a h : ℕ) (c : Fin h) :
    ∃ k, a ≤ k ∧ k < a+h ∧ k%h = c.val := by
  have hp : 0 < h := Nat.zero_lt_of_lt c.isLt
  have hr := Nat.mod_lt a hp
  have he := Nat.mod_add_div a h
  have hc := c.isLt
  by_cases hle : a%h ≤ c.val
  · refine ⟨h*(a/h)+c.val, by omega, by omega, ?_⟩
    simp [Nat.add_mod, Nat.mod_eq_of_lt hc]
  · refine ⟨h*(a/h)+h+c.val, by omega, by omega, ?_⟩
    simp [Nat.add_mod, Nat.mod_eq_of_lt hc]

/-- The intervals active at a point form one consecutive run in the start order.
    Every color is represented when at least as many intervals are active as there are colors. -/
theorem cyclic_cover {n h : ℕ} (start : Fin n → ℝ) (mono : Monotone start)
    (c : Fin h) (x : ℝ)
    (many : h ≤ (Finset.univ.filter fun i => x ∈ Icc (start i) (start i+1)).card) :
    ∃ i : Fin n, i.val%h = c.val ∧ x ∈ Icc (start i) (start i+1) := by
  classical
  let active := Finset.univ.filter fun i => x ∈ Icc (start i) (start i+1)
  have pos : 0 < active.card := lt_of_lt_of_le (Nat.zero_lt_of_lt c.isLt) many
  have nonempty := Finset.card_pos.mp pos
  let lo := active.min' nonempty
  let hi := active.max' nonempty
  have lm : lo ∈ active := active.min'_mem nonempty
  have hm : hi ∈ active := active.max'_mem nonempty
  have inclusion : active.image Fin.val ⊆ Finset.Icc lo.val hi.val := by
    intro k hk
    obtain ⟨i, him, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Icc.mpr ⟨active.min'_le i him, active.le_max' i him⟩
  have count := Finset.card_le_card inclusion
  rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Icc] at count
  obtain ⟨k, lk, kh, kc⟩ := window_residue lo.val h c
  have bound : k ≤ hi.val := by change h ≤ active.card at many; omega
  let i : Fin n := ⟨k, lt_of_le_of_lt bound hi.isLt⟩
  have lox := (Finset.mem_filter.mp lm).2
  have hix := (Finset.mem_filter.mp hm).2
  have li : lo ≤ i := lk
  have ih : i ≤ hi := bound
  exact ⟨i,kc,(mono ih).trans hix.1, lox.2.trans (by linarith [mono li])⟩

/-- Geometric construction of an induced minor. The target intervals have gaps greater
    than two between disjoint pairs and lie in a segment of sufficient coverage. -/
theorem dense_segment_model {n h : ℕ} (start : Fin n → ℝ) (mono : Monotone start)
    (L R : Fin h → ℝ) (ends : ∀ i, L i ≤ R i) (a b : ℝ)
    (inside : ∀ i, a ≤ L i ∧ R i ≤ b)
    (gaps : ∀ i j, R i < L j → R i + 2 < L j)
    (height : ∀ x ∈ Icc a b,
      h ≤ (Finset.univ.filter fun i => x ∈ Icc (start i) (start i+1)).card) :
    IsInducedMinor (intervalGraph L R) (unitGraph start) := by
  classical
  let bag (i : Fin h) := Finset.univ.filter fun k : Fin n =>
    k.val%h = i.val ∧ (Icc (L i) (R i) ∩ Icc (start k) (start k+1)).Nonempty
  have mem {i : Fin h} {k : Fin n} : k ∈ bag i ↔
      k.val%h = i.val ∧ (Icc (L i) (R i) ∩ Icc (start k) (start k+1)).Nonempty := by
    simp only [bag,Finset.mem_filter, Finset.mem_univ, true_and]
  have cover (i : Fin h) (x : ℝ) (hx : x ∈ Icc (L i) (R i)) :
      ∃ k ∈ bag i, x ∈ Icc (start k) (start k+1) := by
    obtain ⟨k,hc,hk⟩ := cyclic_cover start mono i x
      (height x ⟨(inside i).1.trans hx.1,hx.2.trans (inside i).2⟩)
    exact ⟨k,mem.mpr ⟨hc,x,hx,hk⟩,hk⟩
  refine ⟨{ bag := bag, inhabited := ?_, connected := ?_, separate := ?_, edges := ?_ }⟩
  · intro i
    obtain ⟨k,hk,_⟩ := cover i (L i) (left_mem_Icc.mpr (ends i))
    exact ⟨k,hk⟩
  · exact fun i => contains_connected _ _ _ _ _ (ends i) (fun _ hk => (mem.mp hk).2) (cover i)
  · intro i j ne
    exact Finset.disjoint_left.mpr fun k hi hj =>
      ne (Fin.ext ((mem.mp hi).1.symm.trans (mem.mp hj).1))
  · intro i j nij
    constructor
    · rintro ⟨_,x,hxi,hxj⟩
      obtain ⟨v,hv,hvx⟩ := cover i x hxi
      obtain ⟨w,hw,hwx⟩ := cover j x hxj
      refine ⟨v,hv,w,hw,?_,x,hvx,hwx⟩
      rintro rfl
      exact nij (Fin.ext ((mem.mp hv).1.symm.trans (mem.mp hw).1))
    · rintro ⟨v,hv,w,hw,_,z,hzv,hzw⟩
      obtain ⟨x,hxi,hxv⟩ := (mem.mp hv).2
      obtain ⟨y,hyj,hyw⟩ := (mem.mp hw).2
      have e₁ : L j ≤ R i := by
        by_contra! contra
        linarith [(gaps i j contra), hxi.2, hyj.1, hxv.1, hxv.2, hyw.1, hyw.2,
          hzv.1, hzv.2, hzw.1, hzw.2]
      have e₂ : L i ≤ R j := by
        by_contra! contra
        linarith [(gaps j i contra), hxi.1, hyj.2, hxv.1, hxv.2, hyw.1, hyw.2,
          hzv.1, hzv.2, hzw.1, hzw.2]
      exact ⟨nij, max (L i) (L j), ⟨le_max_left _ _, max_le (ends i) e₁⟩,
        ⟨le_max_right _ _, max_le e₂ (ends j)⟩⟩

end UnitIntervalMinors
