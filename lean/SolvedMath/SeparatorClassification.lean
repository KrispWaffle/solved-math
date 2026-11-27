import SolvedMath.WindowCutoff

/-! A bounded rank criterion for the separator question in Part I, §7, item 5. -/

namespace SolvedMath.PatternSeparator

/-- Separator condition stated using only weak comparisons, so that the same
physical position may be represented in several rows. -/
structure OrderSeparator {α : Type} (R : α → α → Prop) (z : α) : Prop where
  compares : ∀ x, R x z ∨ R z x
  lower : ∃ x y, R x z ∧ R y z ∧ ¬R x y ∧ ¬R y x
  upper : ∃ x y, R z x ∧ R z y ∧ ¬R x y ∧ ¬R y x

private structure Match {α β : Type} (R : α → α → Prop) (T : β → β → Prop)
    (z x y : α) (Z X Y : β) : Prop where
  zx : R z x ↔ T Z X
  xz : R x z ↔ T X Z
  zy : R z y ↔ T Z Y
  yz : R y z ↔ T Y Z
  xy : R x y ↔ T X Y
  yx : R y x ↔ T Y X

private theorem Match.inverse {R : α → α → Prop} {T : β → β → Prop} {z x y Z X Y}
    (h : Match R T z x y Z X Y) : Match T R Z X Y z x y :=
  ⟨h.zx.symm,h.xz.symm,h.zy.symm,h.yz.symm,h.xy.symm,h.yx.symm⟩

private theorem transfer_separator {R : α → α → Prop} {T : β → β → Prop} {z Z}
    (forth : ∀ x y, ∃ X Y, Match R T z x y Z X Y)
    (back : ∀ X Y, ∃ x y, Match T R Z X Y z x y)
    (h : OrderSeparator R z) : OrderSeparator T Z := by
  constructor
  · intro X
    obtain ⟨x, _, w⟩ := back X X
    exact (h.compares x).elim (fun h => Or.inl (w.xz.mpr h)) (fun h => Or.inr (w.zx.mpr h))
  · obtain ⟨x,y,hx,hy,xy,yx⟩ := h.lower
    obtain ⟨X,Y,w⟩ := forth x y
    exact ⟨X,Y,w.xz.mp hx,w.yz.mp hy,fun e => xy (w.xy.mpr e),fun e => yx (w.yx.mpr e)⟩
  · obtain ⟨x,y,hx,hy,xy,yx⟩ := h.upper
    obtain ⟨X,Y,w⟩ := forth x y
    exact ⟨X,Y,w.zx.mp hx,w.zy.mp hy,fun e => xy (w.xy.mpr e),fun e => yx (w.yx.mpr e)⟩

private theorem Below.vertices {k} {p : Permutation k} {d j x y}
    (h : Below p d j x y) : Vertex k d j x ∧ Vertex k d j y := by
  induction h with
  | window t i l ht hi hl _ => exact ⟨⟨t,ht,i,hi,rfl⟩,⟨t,ht,l,hl,rfl⟩⟩
  | trans _ _ xy yz => exact ⟨xy.1,yz.2⟩

private theorem incomparable_weak {k} {p : Permutation k} {d j x y} :
    Incomparable p d j x y ↔ ¬Weak p d j x y ∧ ¬Weak p d j y x := by
  constructor
  · rintro ⟨ne, xy, yx⟩
    exact ⟨fun h => h.elim ne xy, fun h => h.elim (fun he => ne he.symm) yx⟩
  · rintro ⟨xy,yx⟩
    exact ⟨fun he => xy (Or.inl he), fun h => xy (Or.inr h), fun h => yx (Or.inr h)⟩

private abbrev Point (k d j : Nat) := {x : Nat // Vertex k d j x}

private def pointLe {k} (p : Permutation k) {d j} (x y : Point k d j) : Prop :=
  Weak p d j x.val y.val

private theorem strict_lower {k} {p : Permutation k} {d j x y z}
    (hx : Weak p d j x z) (hy : Weak p d j y z) (apart : ¬ Weak p d j y x) : Below p d j x z := by
  rcases hx with rfl | h
  · exact False.elim (apart hy)
  · exact h

private theorem strict_upper {k} {p : Permutation k} {d j x y z}
    (hx : Weak p d j z x) (hy : Weak p d j z y) (apart : ¬ Weak p d j x y) : Below p d j z x := by
  rcases hx with rfl | h
  · exact False.elim (apart hy)
  · exact h

private theorem point_separator {k} (p : Permutation k) {d j} (z : Point k d j) :
    IsSeparator p d j z.val ↔ OrderSeparator (pointLe p) z := by
  constructor
  · intro h
    constructor
    · intro x
      rcases h.compares x.val x.property with eq | xz | zx
      · exact Or.inl (Or.inl eq)
      · exact Or.inl (Or.inr xz)
      · exact Or.inr (Or.inr zx)
    · obtain ⟨x,y,hx,hy,apart⟩ := h.lower
      exact ⟨⟨x,hx.vertices.1⟩,⟨y,hy.vertices.1⟩,Or.inr hx,Or.inr hy,incomparable_weak.mp apart⟩
    · obtain ⟨x,y,hx,hy,apart⟩ := h.upper
      exact ⟨⟨x,hx.vertices.2⟩,⟨y,hy.vertices.2⟩,Or.inr hx,Or.inr hy,incomparable_weak.mp apart⟩
  · intro h
    constructor
    · exact z.property
    · intro x hx
      rcases h.compares ⟨x,hx⟩ with (eq | xz) | (eq | zx)
      · exact Or.inl eq
      · exact Or.inr (Or.inl xz)
      · exact Or.inl eq.symm
      · exact Or.inr (Or.inr zx)
    · obtain ⟨x,y,hx,hy,xy,yx⟩ := h.lower
      exact ⟨x.val,y.val,strict_lower hx hy yx,strict_lower hy hx xy,incomparable_weak.mpr ⟨xy,yx⟩⟩
    · obtain ⟨x,y,hx,hy,xy,yx⟩ := h.upper
      exact ⟨x.val,y.val,strict_upper hx hy xy,strict_upper hy hx yx,incomparable_weak.mpr ⟨xy,yx⟩⟩

/-- A window index and a rank within a pattern, both zero-based. -/
abbrev RankSlot (k j : Nat) := Fin j × Fin k

def rankLe {k j} (p : Permutation k) (m d : Nat) (x y : RankSlot k j) : Prop :=
  threshold p m d x.1.val x.2.val y.1.val ≤ y.2.val

/-- This predicate uses only the two lists of boundary ranks. -/
def RankTest {k} (p : Permutation k) (m d j : Nat) : Prop :=
  ∃ z : RankSlot k j, OrderSeparator (rankLe p m d) z

def HasSeparator {k} (p : Permutation k) (d j : Nat) : Prop :=
  ∃ z, IsSeparator p d j z

private def Represents {k} (p : Permutation k) {d j}
    (x : Point k d j) (X : RankSlot k j) : Prop :=
  ∃ i < k, x.val = d*X.1.val+i ∧ p.rank i = X.2.val

private theorem slot_of_point {k} (p : Permutation k) {d j} (x : Point k d j) :
    ∃ X, Represents p x X := by
  obtain ⟨t,ht,i,hi,hx⟩ := x.property
  exact ⟨(⟨t,ht⟩,⟨p.rank i,p.bounded hi⟩),i,hi,hx,rfl⟩

private theorem point_of_slot {k} (p : Permutation k) (d : Nat) {j} (X : RankSlot k j) :
    ∃ x : Point k d j, Represents p x X := by
  obtain ⟨i,hi,hr⟩ := p.onto X.2.isLt
  exact ⟨⟨_,⟨X.1.val,X.1.isLt,i,hi,rfl⟩⟩,i,hi,rfl,hr⟩

namespace Compatible

variable {k m d : Nat} {p : Permutation k} (H : Compatible p m d)
include H

private theorem reps_compare {j} {x y : Point k d j} {X Y : RankSlot k j}
    (hx : Represents p x X) (hy : Represents p y Y) :
    pointLe p x y ↔ rankLe p m d X Y := by
  obtain ⟨i,hi,xe,ri⟩ := hx
  obtain ⟨l,hl,ye,rl⟩ := hy
  unfold pointLe rankLe
  rw [xe, ye, H.weak_iff_threshold X.1.isLt Y.1.isLt hi hl, ri, rl]

private theorem reps_match {j} {z x y : Point k d j} {Z X Y : RankSlot k j}
    (hz : Represents p z Z) (hx : Represents p x X) (hy : Represents p y Y) :
    Match (pointLe p) (rankLe p m d) z x y Z X Y :=
  ⟨H.reps_compare hz hx,H.reps_compare hx hz,H.reps_compare hz hy,
    H.reps_compare hy hz,H.reps_compare hx hy,H.reps_compare hy hx⟩

private theorem slot_separator {j} {z : Point k d j} {Z : RankSlot k j} (hz : Represents p z Z) :
    IsSeparator p d j z.val ↔ OrderSeparator (rankLe p m d) Z := by
  rw [point_separator p z]
  have forth : ∀ x y, ∃ X Y, Match (pointLe p) (rankLe p m d) z x y Z X Y := by
    intro x y
    obtain ⟨X,hx⟩ := slot_of_point p x
    obtain ⟨Y,hy⟩ := slot_of_point p y
    exact ⟨X,Y,H.reps_match hz hx hy⟩
  have back : ∀ X Y, ∃ x y, Match (rankLe p m d) (pointLe p) Z X Y z x y := by
    intro X Y
    obtain ⟨x,hx⟩ := point_of_slot p d X
    obtain ⟨y,hy⟩ := point_of_slot p d Y
    exact ⟨x,y,(H.reps_match hz hx hy).inverse⟩
  exact ⟨transfer_separator forth back,transfer_separator back forth⟩

theorem hasSeparator_iff_rankTest (j : Nat) : HasSeparator p d j ↔ RankTest p m d j := by
  constructor
  · rintro ⟨z,h⟩
    obtain ⟨Z,hz⟩ := slot_of_point p ⟨z,h.vertex⟩
    exact ⟨Z,(H.slot_separator hz).mp h⟩
  · rintro ⟨Z,h⟩
    obtain ⟨z,hz⟩ := point_of_slot p d Z
    exact ⟨z.val,(H.slot_separator hz).mpr h⟩

end Compatible

private theorem rankLe_gap {k j J m d} (p : Permutation k) {s t : Fin j} {S T : Fin J}
    {r q : Fin k} (gap : SameGap k s.val t.val S.val T.val) :
    rankLe p m d (s,r) (t,q) ↔ rankLe p m d (S,r) (T,q) := by
  unfold rankLe
  rw [threshold_congr p m d (Nat.le_of_lt r.isLt) gap]

private theorem slots_match {k j J m d} (p : Permutation k) (s : Fin j) (S : Fin J) (r : Fin k)
    (fit : ArmsFit k j s.val J S.val) (x y : RankSlot k j) :
    ∃ X Y, Match (rankLe p m d) (rankLe p m d) (s,r) x y (S,r) X Y := by
  obtain ⟨A,hA,B,hB,g⟩ := fit.match_two s.isLt S.isLt x.1.isLt y.1.isLt
  refine ⟨(⟨A,hA⟩,x.2),(⟨B,hB⟩,y.2),?_⟩
  exact ⟨rankLe_gap p g.sa,rankLe_gap p g.sa.reverse,
    rankLe_gap p g.sb,rankLe_gap p g.sb.reverse,rankLe_gap p g.ab,rankLe_gap p g.ab.reverse⟩

theorem rankTest_length_congr {k m d j J} (p : Permutation k)
    (h : min (4*k+1) j = min (4*k+1) J) : RankTest p m d j → RankTest p m d J := by
  rintro ⟨⟨s,r⟩,z⟩
  obtain ⟨S,hS,fwd,rev⟩ := match_center s.isLt h
  exact ⟨(⟨S,hS⟩,r),transfer_separator
    (slots_match p s ⟨S,hS⟩ r fwd) (slots_match p ⟨S,hS⟩ s r rev) z⟩

/-- The separator spectrum of a fixed pattern is constant from 4k+1 onward.
The entire spectrum is computed by tests on the boundary ranks. -/
theorem separator_iff_bounded_rankTest {k m d} {p : Permutation k} (H : Compatible p m d) (j : Nat) :
    HasSeparator p d j ↔ RankTest p m d (min (4*k+1) j) := by
  rw [H.hasSeparator_iff_rankTest]
  have hh : min (4*k+1) j = min (4*k+1) (min (4*k+1) j) := by omega
  exact ⟨rankTest_length_congr p hh,rankTest_length_congr p hh.symm⟩

/-- The uniform reading of BKS Part I, §7 item 5. Whether a separator exists at
every occurrence count above the overlap is decided by one finite rank test per
count between m+1 and 4k+1 inclusive. -/
theorem uniform_separator_iff {k m d} {p : Permutation k} (H : Compatible p m d) :
    (∀ j, m < j → HasSeparator p d j) ↔
      ∀ j, m < j → j ≤ 4*k+1 → RankTest p m d j := by
  constructor
  · exact fun h j hj _ => (H.hasSeparator_iff_rankTest j).mp (h j hj)
  · intro h j hj
    apply (separator_iff_bounded_rankTest H j).mpr
    have hlen := H.length_eq
    have hd := H.stride_pos
    exact h _ (by omega) (Nat.min_le_left ..)

private instance slotExists {k j} (P : RankSlot k j → Prop) [DecidablePred P] :
    Decidable (∃ x, P x) := decidable_of_iff _ Prod.exists.symm

private instance slotForall {k j} (P : RankSlot k j → Prop) [DecidablePred P] :
    Decidable (∀ x, P x) := decidable_of_iff _ Prod.forall.symm

private instance rankLeDec {k j m d} {p : Permutation k} (x y : RankSlot k j) :
    Decidable (rankLe p m d x y) := inferInstanceAs (Decidable (_ ≤ _))

private instance sepDec {k j} (R : RankSlot k j → RankSlot k j → Prop) [DecidableRel R]
    (z : RankSlot k j) : Decidable (OrderSeparator R z) :=
  decidable_of_iff
    ((∀ x, R x z ∨ R z x) ∧
      (∃ x y, R x z ∧ R y z ∧ ¬R x y ∧ ¬R y x) ∧
      (∃ x y, R z x ∧ R z y ∧ ¬R x y ∧ ¬R y x))
    ⟨fun ⟨c,l,u⟩ => ⟨c,l,u⟩,fun h => ⟨h.compares,h.lower,h.upper⟩⟩

private instance rankTestDec {k} (p : Permutation k) (m d j : Nat) :
    Decidable (RankTest p m d j) := inferInstanceAs (Decidable (∃ _, _))

/-- Boolean answer at any specified window count, including counts beyond the cutoff. -/
def separatorAt {k} (p : Permutation k) (m j : Nat) : Bool :=
  decide (RankTest p m (k-m) (min (4*k+1) j))

/-- Boolean answer for all window counts strictly greater than the overlap. -/
def separatorAlways {k} (p : Permutation k) (m : Nat) : Bool :=
  decide (∀ j : Fin (4*k+2), m < j.val → RankTest p m (k-m) j.val)

private theorem compatible_of_source {k m} {p : Permutation k} (hm : 1 ≤ m ∧ m < k)
    (iso : ∀ i < m, ∀ l < m, p.rank i < p.rank l ↔ p.rank (k-m+i) < p.rank (k-m+l)) :
    Compatible p m (k-m) := by
  refine ⟨by omega,by omega,?_⟩
  intro i hi q hq
  have := iso q hq i hi
  omega

/-- BKS Part I §7 item 5 at a specified count, under the overlap convention
from §3. The algorithm's work is bounded in terms of k even for unbounded j. -/
theorem bks_separator_at {k m j} (p : Permutation k) (hm : 1 ≤ m ∧ m < k)
    (iso : ∀ i < m, ∀ l < m, p.rank i < p.rank l ↔ p.rank (k-m+i) < p.rank (k-m+l)) :
    separatorAt p m j = true ↔ ∃ z, IsSeparator p (k-m) j z := by
  rw [separatorAt, decide_eq_true_eq]
  exact (separator_iff_bounded_rankTest (compatible_of_source hm iso) j).symm

/-- BKS Part I §7 item 5 with the window count universally quantified above m. -/
theorem bks_separator_always {k m} (p : Permutation k) (hm : 1 ≤ m ∧ m < k)
    (iso : ∀ i < m, ∀ l < m, p.rank i < p.rank l ↔ p.rank (k-m+i) < p.rank (k-m+l)) :
    separatorAlways p m = true ↔ ∀ j, m < j → ∃ z, IsSeparator p (k-m) j z := by
  rw [separatorAlways, decide_eq_true_eq]
  change _ ↔ ∀ j, m < j → HasSeparator p (k-m) j
  rw [uniform_separator_iff (compatible_of_source hm iso)]
  constructor
  · exact fun h j hj bound => h ⟨j,by omega⟩ hj
  · exact fun h j hj => h j.val hj (by have := j.isLt; omega)

end SolvedMath.PatternSeparator
