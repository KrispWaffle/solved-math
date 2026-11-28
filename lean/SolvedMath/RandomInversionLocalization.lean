import SolvedMath.RandomInversionRectangles
import Mathlib.Data.Fin.Rev

namespace RandomInversionConnectivity
open Finset
noncomputable section

def initial (n w : Nat) : Finset (Fin n) := univ.filter (fun x => x.val < w)

@[simp] theorem mem_initial {n w} {x : Fin n} : x ∈ initial n w ↔ x.val < w := by simp [initial]

theorem card_initial {n w : Nat} (h : w < n) : (initial n w).card = w := by
  have e : initial n w = Iio (⟨w,h⟩ : Fin n) := by ext x; simp [Fin.lt_def]
  rw [e,Fin.card_Iio]

def nearPairs (n w d : Nat) : Finset (Fin n × Fin n) :=
  ((initial n w) ×ˢ (initial n w)).filter (fun p =>
    p.1 ≠ p.2 ∧ p.1.val ≤ p.2.val+d ∧ p.2.val ≤ p.1.val+d)

@[simp] theorem mem_near {n w d} {x y : Fin n} : (x,y) ∈ nearPairs n w d ↔
    x.val < w ∧ y.val < w ∧ x ≠ y ∧ x.val ≤ y.val+d ∧ y.val ≤ x.val+d := by
  simp [nearPairs,and_assoc]

theorem near_distinct {n w d} (p : Fin n × Fin n) (hp : p ∈ nearPairs n w d) : p.1 ≠ p.2 :=
  (mem_filter.mp hp).2.1

theorem card_near (n w d : Nat) : (nearPairs n w d).card ≤ w*(2*d+1) := by
  have target : ((range w) ×ˢ (range (2*d+1))).card = w*(2*d+1) := by simp
  rw [← target]
  apply card_le_card_of_injOn (fun p : Fin n × Fin n => (p.1.val,p.2.val+d-p.1.val))
  · intro p hp
    obtain ⟨a,b,_,l,h⟩ := mem_near.mp hp
    exact mem_product.mpr ⟨mem_range.mpr a,mem_range.mpr (by dsimp; omega)⟩
  · intro p hp q hq e
    obtain ⟨_,_,_,a,_⟩ := mem_near.mp hp
    obtain ⟨_,_,_,b,_⟩ := mem_near.mp hq
    have e₁ := congrArg Prod.fst e
    have e₂ := congrArg Prod.snd e
    dsimp at e₁ e₂
    exact Prod.ext (Fin.ext e₁) (Fin.ext (by omega))

def bulkColumns (n b : Nat) : Finset (Fin n) := univ \ initial n (n/2+2*b)

def SafeCorner {n} (π : Perm n) (b l : Nat) : Prop :=
  0 < hits π (initial n b) (initial n b) ∧
  2*b < hits π (initial n (32*b)) (bulkColumns n b) ∧
  hits π (initial n (34*b)) (initial n (34*b)) ≤ l ∧
  pairHits π (nearPairs n (34*b) (2*l)) (nearPairs n (34*b) (2*l)) = 0

theorem small_southwest {n} {π : Perm n} {b l} (safe : SafeCorner π b l) {i j : Fin n}
    (half : i.val ≤ n/2) (cheap : (crossing π i j).card ≤ minimumDegree π) :
    (southwest π i j).card ≤ 1 := by
  obtain ⟨occupied,plenty,capacity,spaced⟩ := safe
  obtain ⟨u,hu⟩ := card_pos.mp occupied
  obtain ⟨pos,val⟩ := mem_filter.mp hu
  have up := mem_initial.mp pos
  have uv := mem_initial.mp val
  have degreeBound := (min_le_degree π u).trans (degree_le_coordinates π u)
  have cost := crossing_card π i j
  have popl : (southwest π i j).card ≤ i.val := by
    simpa [Fin.card_Iio] using card_le_card (show southwest π i j ⊆ Iio i from inter_subset_left)
  have popv : (southwest π i j).card ≤ j.val := by
    simpa [valuesBelow,Fin.card_Iio] using
      card_le_card (show southwest π i j ⊆ valuesBelow π j from inter_subset_right)
  have band : j.val ≤ i.val+2*b := by omega
  have il : i.val < 32*b := by
    by_contra! h
    have sub : (initial n (32*b)).filter (fun x => π x ∈ bulkColumns n b) ⊆ crossing π i j := by
      intro x hx
      obtain ⟨px,vx⟩ := mem_filter.mp hx
      have px' := mem_initial.mp px
      have vx' := (mem_sdiff.mp vx).2
      rw [mem_initial] at vx'
      apply mem_crossing.mpr
      exact Or.inl ⟨(by omega : x.val < i.val),(by omega : j.val ≤ (π x).val)⟩
    have ub := card_le_card sub
    unfold hits at plenty
    omega
  have jl : j.val ≤ 34*b := by omega
  have local_position {x : Fin n} (hx : x ∈ southwest π i j) :
      x.val < 34*b ∧ (π x).val < 34*b := by
    have a : x.val < i.val := (mem_southwest.mp hx).1
    have d : (π x).val < j.val := (mem_southwest.mp hx).2
    omega
  have contained : southwest π i j ⊆ (initial n (34*b)).filter (fun x => π x ∈ initial n (34*b)) := by
    intro x hx
    have ⟨p,v⟩ := local_position hx
    exact mem_filter.mpr ⟨mem_initial.mpr p,mem_initial.mpr v⟩
  have count := (card_le_card contained).trans capacity
  by_contra! large
  obtain ⟨p,q,hp,hq,ne⟩ := one_lt_card_iff.mp large
  have dp := corner_distance hp cheap
  have dq := corner_distance hq cheap
  have p₁ : p.val < i.val := (mem_southwest.mp hp).1
  have p₂ : (π p).val < j.val := (mem_southwest.mp hp).2
  have q₁ : q.val < i.val := (mem_southwest.mp hq).1
  have q₂ : (π q).val < j.val := (mem_southwest.mp hq).2
  obtain ⟨wp,vp⟩ := local_position hp
  obtain ⟨wq,vq⟩ := local_position hq
  have nr : (p,q) ∈ nearPairs n (34*b) (2*l) := mem_near.mpr ⟨wp,wq,ne,by omega,by omega⟩
  have nv : (π p,π q) ∈ nearPairs n (34*b) (2*l) :=
    mem_near.mpr ⟨vp,vq,fun e => ne (π.injective e),by omega,by omega⟩
  have found : 0 < pairHits π (nearPairs n (34*b) (2*l)) (nearPairs n (34*b) (2*l)) :=
    card_pos.mpr ⟨(p,q),mem_filter.mpr ⟨nr,nv⟩⟩
  omega

/-- Reverse positions and complement values. This permutes the sample space. -/
def flip {n} (π : Perm n) : Perm n := (Fin.revPerm.trans π).trans Fin.revPerm

@[simp] theorem flip_apply {n} (π : Perm n) (x : Fin n) : flip π x = (π x.rev).rev := rfl

@[simp] theorem flip_flip {n} (π : Perm n) : flip (flip π) = π := by ext x; simp

def flipEquiv (n : Nat) : Perm n ≃ Perm n := ⟨flip,flip,flip_flip,flip_flip⟩

private theorem map_rev {n} {s : Finset (Fin n)} {x} :
    x.rev ∈ s.map Fin.revPerm.toEmbedding ↔ x ∈ s := mem_map' Fin.revPerm.toEmbedding

theorem flip_degree {n} (π : Perm n) (x : Fin n) : degree (flip π) x.rev = degree π x := by
  have seteq : univ.filter (Edge (flip π) x.rev) =
      (univ.filter (Edge π x)).map Fin.revPerm.toEmbedding := by
    ext y
    obtain ⟨y,rfl⟩ := Fin.rev_surjective y
    rw [map_rev]
    simp [Edge,or_comm]
  simp [degree,seteq]

theorem flip_minimumDegree {n} (π : Perm n) : minimumDegree (flip π) = minimumDegree π := by
  have seteq : univ.image (degree (flip π)) = univ.image (degree π) := by
    ext a
    simp only [mem_image,mem_univ,true_and]
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨x.rev,by simpa using (flip_degree π x.rev).symm⟩
    · rintro ⟨x,rfl⟩
      exact ⟨x.rev,flip_degree π x⟩
  simp [minimumDegree,seteq]

def mirror {n} (i : Fin n) (pos : 0 < i.val) : Fin n := ⟨n-i.val,by omega⟩

private theorem mirror_left {n} {x i : Fin n} (hi : 0 < i.val) :
    x.rev < mirror i hi ↔ i ≤ x := by
  change n-(x.val+1) < n-i.val ↔ i.val ≤ x.val
  have := x.isLt
  have := i.isLt
  omega

theorem flip_scan {n} (π : Perm n) (i j : Fin n) (hi : 0 < i.val) (hj : 0 < j.val) :
    (southwest (flip π) (mirror i hi) (mirror j hj)).card = (northeast π i j).card ∧
    (crossing (flip π) (mirror i hi) (mirror j hj)).card = (crossing π i j).card := by
  have sw : southwest (flip π) (mirror i hi) (mirror j hj) =
      (northeast π i j).map Fin.revPerm.toEmbedding := by
    ext y
    obtain ⟨y,rfl⟩ := Fin.rev_surjective y
    rw [map_rev]
    simp [mirror_left]
  have cr : crossing (flip π) (mirror i hi) (mirror j hj) =
      (crossing π i j).map Fin.revPerm.toEmbedding := by
    ext y
    obtain ⟨y,rfl⟩ := Fin.rev_surjective y
    rw [map_rev]
    simp only [mem_crossing,flip_apply,Fin.rev_rev]
    have a := mirror_left (x := y) hi
    have b := mirror_left (x := π y) hj
    grind
  simp [sw,cr]

theorem equality_of_safe_corners {n} {π : Perm n} {b l} (lower : SafeCorner π b l)
    (upper : SafeCorner (flip π) b l) : vertexConnectivity π = minimumDegree π := by
  apply equality_of_singleton_scans
  intro i j sw _ cheap
  by_cases first : i.val ≤ n/2
  · exact Or.inl (small_southwest lower first cheap)
  · obtain ⟨x,hx⟩ := sw
    have hi : 0 < i.val := Nat.zero_lt_of_lt (mem_southwest.mp hx).1
    have hj : 0 < j.val := Nat.zero_lt_of_lt (mem_southwest.mp hx).2
    have ⟨a,c⟩ := flip_scan π i j hi hj
    apply Or.inr
    rw [←a]
    apply small_southwest upper (by dsimp [mirror]; omega)
    rwa [c,flip_minimumDegree]

end
end RandomInversionConnectivity
