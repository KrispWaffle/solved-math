module

public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Logic.Relation
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace RandomInversionConnectivity

open Finset Filter
open scoped Topology

abbrev Perm (n : Nat) := Equiv.Perm (Fin n)

def Edge {n} (π : Perm n) (x y : Fin n) : Prop :=
  (x < y ∧ π y < π x) ∨ (y < x ∧ π x < π y)

instance {n} (π : Perm n) (x y : Fin n) : Decidable (Edge π x y) := by
  unfold Edge
  infer_instance

theorem edge_symm {n} {π : Perm n} {x y} (h : Edge π x y) : Edge π y x := h.symm

def degree {n} (π : Perm n) (x : Fin n) : Nat := (univ.filter (Edge π x)).card

def minimumDegree {n} (π : Perm n) : Nat :=
  (insert (n-1) (univ.image (degree π))).min' (insert_nonempty ..)

theorem min_le_degree {n} (π : Perm n) (x : Fin n) : minimumDegree π ≤ degree π x := by
  apply min'_le
  exact mem_insert_of_mem (mem_image_of_mem _ (mem_univ x))

/-- A path using only the retained vertices, as an ordinary reflexive transitive closure. -/
def Path {n} (π : Perm n) (keep : Finset (Fin n)) :=
  Relation.ReflTransGen (fun x y => x ∈ keep ∧ y ∈ keep ∧ Edge π x y)

theorem path_reverse {n} {π : Perm n} {keep} {x y}
    (p : Path π keep x y) : Path π keep y x := by
  induction p with
  | refl => exact .refl
  | tail _ step ih =>
    apply Relation.ReflTransGen.trans _ ih
    exact .single ⟨step.2.1,step.1,edge_symm step.2.2⟩

def Separates {n} (π : Perm n) (gone : Finset (Fin n)) : Prop :=
  ∃ x ∈ univ \ gone, ∃ y ∈ univ \ gone, ¬ Path π (univ \ gone) x y

noncomputable def vertexConnectivity {n} (π : Perm n) : Nat := by
  classical
  exact (insert (n-1) (((univ : Finset (Fin n)).powerset.filter (Separates π)).image card)).min'
    (insert_nonempty ..)

theorem connectivity_le_cut {n} {π : Perm n} {s} (h : Separates π s) :
    vertexConnectivity π ≤ s.card := by
  classical
  apply min'_le
  exact mem_insert_of_mem (mem_image_of_mem _ (mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _),h⟩))

def valuesBelow {n} (π : Perm n) (j : Fin n) : Finset (Fin n) :=
  (Iio j).map π.symm.toEmbedding

@[simp] theorem mem_valuesBelow {n} {π : Perm n} {j x : Fin n} :
    x ∈ valuesBelow π j ↔ π x < j := by
  simp [valuesBelow]

def southwest {n} (π : Perm n) (i j : Fin n) : Finset (Fin n) :=
  Iio i ∩ valuesBelow π j

def crossing {n} (π : Perm n) (i j : Fin n) : Finset (Fin n) :=
  (Iio i \ valuesBelow π j) ∪ (valuesBelow π j \ Iio i)

@[simp] theorem mem_southwest {n} {π : Perm n} {x i j : Fin n} :
    x ∈ southwest π i j ↔ x < i ∧ π x < j := by simp [southwest]

@[simp] theorem mem_crossing {n} {π : Perm n} {x i j : Fin n} :
    x ∈ crossing π i j ↔ (x < i ∧ j ≤ π x) ∨ (i ≤ x ∧ π x < j) := by
  simp [crossing, and_comm]

theorem crossing_card {n} (π : Perm n) (i j : Fin n) :
    (crossing π i j).card + 2*(southwest π i j).card = i.val + j.val := by
  let l := Iio i
  let v := valuesBelow π j
  have hdis : Disjoint (l \ v) (v \ l) := by
    apply disjoint_left.mpr
    intro x h h'
    exact (mem_sdiff.mp h).2 (mem_sdiff.mp h').1
  have left := card_sdiff_add_card_inter l v
  have right := card_sdiff_add_card_inter v l
  rw [inter_comm v l] at right
  have lc : l.card = i.val := Fin.card_Iio ..
  have vc : v.card = j.val := by simp [v,valuesBelow,Fin.card_Iio]
  change ((l \ v) ∪ (v \ l)).card + 2*(l ∩ v).card = _
  rw [card_union_of_disjoint hdis]
  omega

theorem degree_le_coordinates {n} (π : Perm n) (x : Fin n) :
    degree π x ≤ x.val + (π x).val := by
  have sub : univ.filter (Edge π x) ⊆ Iio x ∪ valuesBelow π (π x) := by
    intro y hy
    rcases (mem_filter.mp hy).2 with h | h
    · exact mem_union_right _ (mem_valuesBelow.mpr h.2)
    · exact mem_union_left _ (mem_Iio.mpr h.1)
  simpa [degree,valuesBelow,Fin.card_Iio] using (card_le_card sub).trans (card_union_le ..)

/-- In a southwest rectangle whose separator is at most the minimum degree,
every point must be within twice the population of the upper right corner. -/
theorem corner_distance {n} {π : Perm n} {i j x : Fin n} (hx : x ∈ southwest π i j)
    (cheap : (crossing π i j).card ≤ minimumDegree π) :
    (i.val - x.val) + (j.val - (π x).val) ≤ 2*(southwest π i j).card := by
  obtain ⟨xp,xv⟩ := mem_southwest.mp hx
  have xp' : x.val < i.val := xp
  have xv' : (π x).val < j.val := xv
  have bound := (cheap.trans (min_le_degree π x)).trans (degree_le_coordinates π x)
  have size := crossing_card π i j
  omega

/-- A strict cut with just two southwest points forces consecutive positions
and consecutive values in decreasing order. Thresholds use zero-based ranks. -/
theorem strict_two_point_rectangle {n} {π : Perm n} {i j p q : Fin n}
    (hp : p ∈ southwest π i j) (hq : q ∈ southwest π i j) (order : p < q)
    (two : (southwest π i j).card = 2) (cheap : (crossing π i j).card < minimumDegree π) :
    p.val + 1 = q.val ∧ q.val + 1 = i.val ∧
    (π q).val + 1 = (π p).val ∧ (π p).val + 1 = j.val := by
  have price := crossing_card π i j
  rw [two] at price
  have h₁ := (min_le_degree π p).trans (degree_le_coordinates π p)
  have h₂ := (min_le_degree π q).trans (degree_le_coordinates π q)
  have p₁ : p.val < i.val := (mem_southwest.mp hp).1
  have p₂ : (π p).val < j.val := (mem_southwest.mp hp).2
  have q₁ : q.val < i.val := (mem_southwest.mp hq).1
  have q₂ : (π q).val < j.val := (mem_southwest.mp hq).2
  have pq : p.val < q.val := order
  have distinct : (π p).val ≠ (π q).val := fun h => order.ne (π.injective (Fin.ext h))
  omega

private theorem component_before {n} {π : Perm n} {k : Finset (Fin n)} {a y x : Fin n}
    (ha : a ∈ k) (hy : y ∈ k) (ay : a < y) (miss : ¬Path π k a y)
    (path : Path π k a x) : x < y ∧ π x < π y := by
  have apart {z : Fin n} (hz : z ∈ k) (h : Path π k a z) : ¬Edge π z y :=
    fun e => miss (h.tail ⟨hz,hy,e⟩)
  induction path with
  | refl =>
    have en := apart ha (.refl)
    have ne : π a ≠ π y := fun e => ay.ne (π.injective e)
    exact ⟨ay, lt_of_le_of_ne (le_of_not_gt (fun h => en (Or.inl ⟨ay,h⟩))) ne⟩
  | @tail z u p step ih =>
    have pu : Path π k a u := p.tail step
    have en := apart step.2.1 pu
    have uy : u ≠ y := fun e => miss (e ▸ pu)
    rcases lt_or_gt_of_ne uy with h | h
    · have ne : π u ≠ π y := fun e => uy (π.injective e)
      exact ⟨h,lt_of_le_of_ne (le_of_not_gt (fun h' => en (Or.inl ⟨h,h'⟩))) ne⟩
    · have val : π y ≤ π u := le_of_not_gt (fun h' => en (Or.inr ⟨h,h'⟩))
      rcases step.2.2 with edge | edge
      · exact False.elim ((not_lt_of_ge (ih.2.le.trans val)) edge.2)
      · exact False.elim ((not_lt_of_ge (ih.1.le.trans h.le)) edge.1)

/-- Every vertex cut contains a separating scanline. Both sides have a surviving
vertex, and the thresholds are the first excluded position and value. -/
theorem separator_has_scanline {n} {π : Perm n} {gone : Finset (Fin n)}
    (h : Separates π gone) : ∃ i j : Fin n, crossing π i j ⊆ gone ∧
      (southwest π i j).Nonempty ∧ ∃ z, i ≤ z ∧ j ≤ π z := by
  classical
  let k := univ \ gone
  obtain ⟨u,hu,v,hv,no⟩ := h
  change u ∈ k at hu
  change v ∈ k at hv
  let a := k.min' ⟨u,hu⟩
  have ha : a ∈ k := min'_mem ..
  let other := k.filter (fun y => ¬Path π k a y)
  have on : other.Nonempty := by
    by_cases h : Path π k a u
    · exact ⟨v,mem_filter.mpr ⟨hv,fun h' => no ((path_reverse h).trans h')⟩⟩
    · exact ⟨u,mem_filter.mpr ⟨hu,h⟩⟩
  let i := other.min' on
  let j := (other.image π).min' (on.image π)
  have hi : i ∈ other := min'_mem ..
  have hj : j ∈ other.image π := min'_mem ..
  obtain ⟨y,hy,ey⟩ := mem_image.mp hj
  have before {b x : Fin n} (hb : b ∈ other) (px : Path π k a x) : x < b ∧ π x < π b := by
    obtain ⟨bk,miss⟩ := mem_filter.mp hb
    have lt : a < b := lt_of_le_of_ne (min'_le _ _ bk) (by rintro rfl; exact miss .refl)
    exact component_before ha bk lt miss px
  have region {x : Fin n} (p : Path π k a x) : x < i ∧ π x < j := by
    exact ⟨(before hi p).1, ey ▸ (before hy p).2⟩
  have beyond {x : Fin n} (hx : x ∈ other) : i ≤ x ∧ j ≤ π x :=
    ⟨min'_le _ _ hx,min'_le _ _ (mem_image_of_mem _ hx)⟩
  refine ⟨i,j,?_,⟨a,mem_southwest.mpr (region .refl)⟩,i,beyond hi⟩
  intro x hx
  by_contra hgone
  have hk : x ∈ k := mem_sdiff.mpr ⟨mem_univ _,hgone⟩
  have cross := mem_crossing.mp hx
  by_cases p : Path π k a x
  · have := region p
    grind
  · have := beyond (mem_filter.mpr ⟨hk,p⟩)
    grind

def northeast {n} (π : Perm n) (i j : Fin n) : Finset (Fin n) :=
  univ.filter (fun x => i ≤ x ∧ j ≤ π x)

@[simp] theorem mem_northeast {n} {π : Perm n} {x i j : Fin n} :
    x ∈ northeast π i j ↔ i ≤ x ∧ j ≤ π x := by simp [northeast]

theorem connectivity_le_degree {n} (π : Perm n) (x : Fin n) :
    vertexConnectivity π ≤ degree π x := by
  classical
  have cap : vertexConnectivity π ≤ n-1 := min'_le _ _ (mem_insert_self ..)
  by_cases enough : n-1 ≤ degree π x
  · exact cap.trans enough
  let nb := univ.filter (Edge π x)
  let keep := univ \ nb
  have count := card_sdiff_add_card_eq_card (subset_univ nb)
  change keep.card + degree π x = _ at count
  rw [card_univ,Fintype.card_fin] at count
  obtain ⟨y,hy,ne⟩ := exists_mem_ne (s := keep) (by omega) x
  have hx : x ∈ keep := by simp [keep,nb,Edge]
  apply connectivity_le_cut (s := nb)
  refine ⟨x,hx,y,hy,?_⟩
  intro p
  have fixed {z : Fin n} (h : Path π keep x z) : z=x := by
    induction h with
    | refl => rfl
    | tail _ step ih =>
      have gone := (mem_sdiff.mp step.2.1).2
      exact False.elim (gone (mem_filter.mpr ⟨mem_univ _,ih ▸ step.2.2⟩))
  exact ne (fixed p)

theorem connectivity_le_minimumDegree {n} (π : Perm n) :
    vertexConnectivity π ≤ minimumDegree π := by
  classical
  have mem : minimumDegree π ∈ insert (n-1) (univ.image (degree π)) := min'_mem ..
  rcases mem_insert.mp mem with eq | h
  · rw [eq]
    exact min'_le _ _ (mem_insert_self ..)
  · obtain ⟨x, _, eq⟩ := mem_image.mp h
    rw [← eq]
    exact connectivity_le_degree π x

def SingletonScans {n} (π : Perm n) : Prop :=
  ∀ i j, (southwest π i j).Nonempty → (northeast π i j).Nonempty →
    (crossing π i j).card ≤ minimumDegree π →
    (southwest π i j).card ≤ 1 ∨ (northeast π i j).card ≤ 1

private theorem singleton_bound {n} {π : Perm n} {i j : Fin n}
    (hs : (southwest π i j).Nonempty) (hn : (northeast π i j).Nonempty)
    (one : (southwest π i j).card ≤ 1 ∨ (northeast π i j).card ≤ 1) :
    minimumDegree π ≤ (crossing π i j).card := by
  have sep {x y : Fin n} (a : x ∈ southwest π i j) (b : y ∈ northeast π i j) :
      ¬Edge π x y := by
    obtain ⟨xl,xv⟩ := mem_southwest.mp a
    obtain ⟨yl,yv⟩ := mem_northeast.mp b
    intro e
    rcases e with e | e
    · exact (not_lt_of_ge (xv.le.trans yv)) e.2
    · exact (not_lt_of_ge (xl.le.trans yl)) e.1
  have sides {y : Fin n} (h : y ∉ crossing π i j) :
      y ∈ southwest π i j ∨ y ∈ northeast π i j := by
    simp only [mem_crossing,mem_southwest,mem_northeast] at *
    grind
  rcases one with left | right
  · obtain ⟨x,hx⟩ := hs
    apply (min_le_degree π x).trans (card_le_card ?_)
    intro y hy
    have e := (mem_filter.mp hy).2
    by_contra h
    rcases sides h with yl | yr
    · have eq := card_le_one_iff.mp left hx yl
      simp [eq,Edge] at e
    · exact sep hx yr e
  · obtain ⟨x,hx⟩ := hn
    apply (min_le_degree π x).trans (card_le_card ?_)
    intro y hy
    have e := (mem_filter.mp hy).2
    by_contra h
    rcases sides h with yl | yr
    · exact sep yl hx (edge_symm e)
    · have eq := card_le_one_iff.mp right hx yr
      simp [eq,Edge] at e

/-- If every cheap separating scanline has a singleton side, the ordinary
vertex connectivity is equal to the minimum graph degree. -/
theorem equality_of_singleton_scans {n} {π : Perm n} (good : SingletonScans π) :
    vertexConnectivity π = minimumDegree π := by
  classical
  apply Nat.le_antisymm (connectivity_le_minimumDegree π)
  have mem : vertexConnectivity π ∈ insert (n-1)
      (((univ : Finset (Fin n)).powerset.filter (Separates π)).image card) := min'_mem ..
  rcases mem_insert.mp mem with eq | h
  · rw [eq]
    exact min'_le _ _ (mem_insert_self ..)
  · obtain ⟨s,hs,eq⟩ := mem_image.mp h
    rw [← eq]
    by_cases large : minimumDegree π ≤ s.card
    · exact large
    obtain ⟨i,j,sub,sw,z,hz⟩ := separator_has_scanline (mem_filter.mp hs).2
    have ne : (northeast π i j).Nonempty := ⟨z,mem_northeast.mpr hz⟩
    have bound := card_le_card sub
    exact (singleton_bound sw ne (good i j sw ne (by omega))).trans bound

noncomputable def equalityProbability (n : Nat) : ℝ := by
  classical
  exact ((univ.filter (fun π : Perm n => vertexConnectivity π = minimumDegree π)).card : ℝ) /
    n.factorial

def VerkamaQuestion : Prop := Tendsto equalityProbability atTop (𝓝 1)

end RandomInversionConnectivity
