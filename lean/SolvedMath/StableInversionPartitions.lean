module

public import SolvedMath.StableInversionLimit

@[expose] public section

namespace StableInversions

/-- A decreasing integer partition and the marks (level, insertion weight), latest first. -/
structure MarkedPartition where
  parts : List ℕ
  marks : List (ℕ × ℕ)
  deriving DecidableEq, Repr

namespace MarkedPartition

def empty : MarkedPartition := ⟨[],[]⟩

def markedLevel : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (c,_)::_ => c+1

def nextWeight : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (_,u)::_ => u+1

def level (t : MarkedPartition) : ℕ := max (t.parts.headD 0) (markedLevel t.marks)

def partitionParts : List ℕ → Prop
  | [] => True
  | b::p => 0<b ∧ p.headD 0 ≤ b ∧ partitionParts p

/-- Both coordinates strictly decrease down the list, and the weight is below its level. -/
def increasingMarks : List (ℕ × ℕ) → Prop
  | [] => True
  | (c,u)::m => markedLevel m ≤ c ∧ nextWeight m ≤ u ∧ u<c ∧ increasingMarks m

def Valid (t : MarkedPartition) : Prop := partitionParts t.parts ∧ increasingMarks t.marks

/-- Add one ordinary part at each start of a run of consecutive marked levels. -/
def markCost : List (ℕ × ℕ) → ℕ
  | [] => 0
  | (c,u)::m => u + (if markedLevel m=c then 0 else c) + markCost m

def weight (t : MarkedPartition) : ℕ := t.parts.sum + markCost t.marks

def size (t : MarkedPartition) : ℕ := t.parts.length + 2*t.marks.length

/-- Add the latest slot; the first mark in a run consumes its mandatory ordinary part. -/
def record (t : MarkedPartition) (i : ℕ) : MarkedPartition :=
  if i<t.level then
    ⟨if markedLevel t.marks=t.level then t.parts else t.parts.tail, (t.level,i)::t.marks⟩
  else ⟨i::t.parts,t.marks⟩

def encode : List ℕ → MarkedPartition
  | [] => empty
  | i::h => (encode h).record i

private theorem head_pos_or_empty (p : List ℕ) (hp : partitionParts p) : p=[] ∨ 0 < p.headD 0 := by
  cases p with
  | nil => exact Or.inl rfl
  | cons a p => exact Or.inr hp.1

private theorem level_positive {t : MarkedPartition} (v : t.Valid) (ne : t ≠ empty) : 0<t.level := by
  obtain ⟨p,m⟩ := t
  rcases head_pos_or_empty p v.1 with rfl | hp
  · cases m with
    | nil => exact (ne rfl).elim
    | cons a m => simp [level,markedLevel]
  · exact lt_of_lt_of_le hp (le_max_left _ _)

/-- A step of the insertion path preserves the actual partition inequalities and adds its slot cost. -/
theorem record_behavior (t : MarkedPartition) (i : ℕ) (v : t.Valid)
    (start : t≠empty ∨ 0 < i) (allow : nextWeight t.marks ≤ i) :
    (t.record i).Valid ∧ (nextWeight (t.record i).marks,(t.record i).level) =
      nextState (nextWeight t.marks,t.level) i ∧ (t.record i).weight=t.weight+i ∧ t.record i≠empty := by
  obtain ⟨p,m⟩ := t
  obtain ⟨hp,hm⟩ := v
  let b := max (p.headD 0) (markedLevel m)
  have pb : p.headD 0 ≤ b := le_max_left _ _
  have mb : markedLevel m ≤ b := le_max_right _ _
  change nextWeight m ≤ i at allow
  change partitionParts p at hp
  change increasingMarks m at hm
  change _ ∧ _ = nextState (nextWeight m,b) i ∧ _ = p.sum+markCost m+i ∧ _
  by_cases marked : i<b
  · by_cases continuation : markedLevel m=b
    · have recorded : record ⟨p,m⟩ i = ⟨p,(b,i)::m⟩ := by
        unfold record; change (if i<b then _ else _) = _; rw [ite_eq_left marked]; change (⟨if markedLevel m=b then p else p.tail, (b,i)::m⟩ : MarkedPartition) = _; rw [ite_eq_left continuation]
      rw [recorded]
      have top : max (p.headD 0) (b+1) = b+1 := by omega
      exact ⟨⟨hp,mb,allow,marked,hm⟩,by
          simp only [nextState, marked, ↓reduceIte]; change (i+1,max (p.headD 0) (b+1))=(i+1,b+1); rw [top],
        by simp [weight,markCost,continuation]; omega, fun e => by cases e⟩
    · have ptop : p.headD 0=b := by dsimp [b]; omega
      cases p with
      | nil => simp at ptop; omega
      | cons j p =>
        change j=b at ptop
        have recorded : record ⟨j::p,m⟩ i = ⟨p,(b,i)::m⟩ := by
          unfold record
          change (if i<b then _ else _) = _
          rw [ite_eq_left marked]
          change (⟨if markedLevel m=b then j::p else p, (b,i)::m⟩ : MarkedPartition) = _
          rw [ite_eq_right continuation]
        rw [recorded]
        obtain ⟨_,pj,hp⟩ := hp
        have top : max (p.headD 0) (b+1) = b+1 := by omega
        exact ⟨⟨hp,mb,allow,marked,hm⟩,by
          simp only [nextState, marked, ↓reduceIte]; change (i+1,max (p.headD 0) (b+1))=(i+1,b+1); rw [top],
          by simp [weight,markCost,continuation,ptop]; omega,fun e => by cases e⟩
  · have recorded : record ⟨p,m⟩ i = ⟨i::p,m⟩ := by unfold record; exact ite_eq_right marked
    rw [recorded]
    have pos : 0 < i := by
      rcases start with ne | hi
      · have := level_positive (t:=⟨p,m⟩) ⟨hp,hm⟩ ne
        change 0<b at this; omega
      · exact hi
    have top : max i (markedLevel m)=i := by omega
    exact ⟨⟨⟨pos,by omega,hp⟩,hm⟩,by simp [nextState,level,marked,top],
      by simp [weight]; omega,fun e => by cases e⟩

theorem encode_behavior {h : List ℕ} (hc : Core h) :
    (encode h).Valid ∧ (nextWeight (encode h).marks,(encode h).level) = state h ∧
    (encode h).weight=h.sum ∧ (h≠[] → encode h≠empty) := by
  induction hc with
  | nil => exact ⟨⟨trivial,trivial⟩,rfl,rfl,fun h => (h rfl).elim⟩
  | @step h i _ start allow ih =>
    obtain ⟨v,st,wt,ne⟩ := ih
    have a : nextWeight (encode h).marks ≤ i := by simpa [← st] using allow
    obtain ⟨v',st',wt',ne'⟩ := record_behavior _ _ v (start.imp_left ne) a
    exact ⟨v', st'.trans (congrArg (fun s => nextState s i) st), wt'.trans (by simp [wt,Nat.add_comm]),fun _ => ne'⟩

/-- Remove the chronologically last event; at a run start restore the mandatory ordinary arrival. -/
def undo (t : MarkedPartition) : Option (ℕ × MarkedPartition) :=
  match t.marks with
  | [] => match t.parts with
    | [] => none
    | a::p => some (a,⟨p,[]⟩)
  | (c,u)::m => if c < t.parts.headD 0 then some (t.parts.headD 0,⟨t.parts.tail,t.marks⟩)
    else some (u,⟨if markedLevel m=c then t.parts else c::t.parts,m⟩)

private theorem undo_ordinary (p : List ℕ) (m : List (ℕ × ℕ)) (i : ℕ) (hi : markedLevel m≤ i) :
    undo ⟨i::p,m⟩ = some (i,⟨p,m⟩) := by
  cases m with
  | nil => rfl
  | cons h m =>
    obtain ⟨c,u⟩ := h
    change c+1≤ i at hi
    change (if c < i then _ else _) = _
    exact ite_eq_left hi

private theorem undo_mark (p : List ℕ) (m : List (ℕ × ℕ)) (c u : ℕ) (hp : p.headD 0≤c) :
    undo ⟨p,(c,u)::m⟩ = some (u,⟨if markedLevel m=c then p else c::p,m⟩) := by
  change (if c < p.headD 0 then _ else _) = _
  exact ite_eq_right (Nat.not_lt.mpr hp)

private theorem record_ordinary (p : List ℕ) (m : List (ℕ × ℕ)) (i : ℕ)
    (bound : level ⟨p,m⟩ ≤ i) : record ⟨p,m⟩ i = ⟨i::p,m⟩ := ite_eq_right (Nat.not_lt.mpr bound)

private theorem record_mark (p : List ℕ) (m : List (ℕ × ℕ)) (c u : ℕ)
    (hb : level ⟨p,m⟩ = c) (hu : u<c) :
    record ⟨p,m⟩ u = ⟨if markedLevel m=c then p else p.tail,(c,u)::m⟩ := by
  unfold record
  rw [hb,ite_eq_left hu]

private theorem weight_floor_le {m : List (ℕ × ℕ)} (v : increasingMarks m) : nextWeight m ≤ markedLevel m := by
  cases m with
  | nil => rfl
  | cons a m =>
    obtain ⟨c,u⟩ := a
    have h : u<c := v.2.2.1
    change u+1 ≤ c+1; omega

/-- Recording a permitted slot can be undone from the two lists alone. -/
theorem undo_record (t : MarkedPartition) (i : ℕ) (v : t.Valid) :
    (t.record i).undo = some (i,t) := by
  obtain ⟨p,m⟩ := t
  have ptop : p.headD 0 ≤ level ⟨p,m⟩ := le_max_left _ _
  have mtop : markedLevel m ≤ level ⟨p,m⟩ := le_max_right _ _
  by_cases mark : i < level ⟨p,m⟩
  · rw [record_mark p m _ i rfl mark]
    by_cases follow : markedLevel m=level ⟨p,m⟩
    · rw [ite_eq_left follow,undo_mark _ _ _ _ ptop,ite_eq_left follow]
    · have eq : p.headD 0=level ⟨p,m⟩ := by change p.headD 0=max (p.headD 0) (markedLevel m); change markedLevel m≠max (p.headD 0) (markedLevel m) at follow; omega
      cases p with
      | nil => change 0=level ⟨[],m⟩ at eq; omega
      | cons b p =>
        change b=level ⟨b::p,m⟩ at eq
        have prev : p.headD 0 ≤ level ⟨b::p,m⟩ := v.1.2.1.trans eq.le
        rw [ite_eq_right follow]
        change undo ⟨p,(level ⟨b::p,m⟩,i)::m⟩ = _
        rw [undo_mark p m _ i prev,ite_eq_right follow]
        simp [← eq]
  · rw [record_ordinary p m i (Nat.le_of_not_gt mark),undo_ordinary p m i (mtop.trans (Nat.le_of_not_gt mark))]

theorem encode_injective {h g : List ℕ} (hc : Core h) (gc : Core g) (eq : encode h=encode g) : h=g := by
  induction hc generalizing g with
  | nil =>
    by_contra! ne
    exact (encode_behavior gc).2.2.2 (Ne.symm ne) eq.symm
  | @step h i hp start allow ih =>
    cases gc with
    | nil => exact ((encode_behavior (Core.step hp start allow)).2.2.2 (by simp) eq).elim
    | @step g j gp _ _ =>
      have both := congrArg undo eq
      change undo ((encode h).record i)=undo ((encode g).record j) at both
      rw [undo_record _ _ (encode_behavior hp).1,undo_record _ _ (encode_behavior gp).1] at both
      have pair := Option.some.inj both
      exact List.cons.injEq _ _ _ _ |>.mpr ⟨congrArg Prod.fst pair,ih gp (congrArg Prod.snd pair)⟩

private def Before (s t : MarkedPartition) (i : ℕ) : Prop :=
  s.Valid ∧ (s≠empty ∨ 0 < i) ∧ nextWeight s.marks≤ i ∧ s.record i=t ∧ s.size < t.size

private theorem before_ordinary (a : ℕ) (p : List ℕ) (m : List (ℕ × ℕ))
    (hp : partitionParts (a::p)) (hm : increasingMarks m) (bound : markedLevel m≤a) :
    Before ⟨p,m⟩ ⟨a::p,m⟩ a := by
  obtain ⟨pos,ptop,prior⟩ := hp
  exact ⟨⟨prior,hm⟩,Or.inr pos,(weight_floor_le hm).trans bound,
    record_ordinary p m a (max_le ptop bound), by simp [size]⟩

private theorem before_mark (p : List ℕ) (m : List (ℕ × ℕ)) (c u : ℕ)
    (hp : partitionParts p) (hm : increasingMarks ((c,u)::m)) (bound : p.headD 0≤c) :
    ∃ s, Before s ⟨p,(c,u)::m⟩ u := by
  obtain ⟨mtop,allowed,small,prior⟩ := hm
  by_cases follow : markedLevel m=c
  · have lev : level ⟨p,m⟩=c := by unfold level; change max (p.headD 0) (markedLevel m)=c; omega
    have nonempty : (⟨p,m⟩ : MarkedPartition) ≠ empty := by
      intro he
      have hz := congrArg level he
      change level ⟨p,m⟩=0 at hz; omega
    refine ⟨⟨p,m⟩,⟨hp,prior⟩,Or.inl nonempty,allowed,?_,by simp [size]⟩
    rw [record_mark p m c u lev small,ite_eq_left follow]
  · have lev : level ⟨c::p,m⟩=c := max_eq_left mtop
    refine ⟨⟨c::p,m⟩,⟨⟨by omega,bound,hp⟩,prior⟩,Or.inl (by intro e; cases e),allowed,?_,by simp [size]; omega⟩
    rw [record_mark (c::p) m c u lev small,ite_eq_right follow]
    rfl

private theorem previous (t : MarkedPartition) (v : t.Valid) (ne : t≠empty) : ∃ s i, Before s t i := by
  obtain ⟨p,m⟩ := t
  obtain ⟨hp,hm⟩ := v
  cases m with
  | nil =>
    cases p with
    | nil => exact (ne rfl).elim
    | cons a p => exact ⟨⟨p,[]⟩,a,before_ordinary a p [] hp hm (Nat.zero_le _)⟩
  | cons m ms =>
    obtain ⟨c,u⟩ := m
    by_cases bound : p.headD 0 ≤ c
    · obtain ⟨s,hs⟩ := before_mark p ms c u hp hm bound
      exact ⟨s,u,hs⟩
    · cases p with
      | nil => simp at bound
      | cons a p =>
        change ¬ a≤c at bound
        exact ⟨⟨p,(c,u)::ms⟩,a,before_ordinary a p ((c,u)::ms) hp hm (show c+1≤a by omega)⟩

/-- Any ordinary partition and admissible marks reconstruct precisely one reduced insertion path. -/
theorem encode_surjective (t : MarkedPartition) (v : t.Valid) : ∃ h, Core h ∧ encode h=t := by
  suffices allSizes : ∀ n (s : MarkedPartition), s.size=n → s.Valid → ∃ h, Core h ∧ encode h=s by
    exact allSizes _ t rfl v
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro t cnt val
    by_cases base : t=empty
    · exact ⟨[],Core.nil,base.symm⟩
    · obtain ⟨s,i,good,start,allow,recorded,smaller⟩ := previous t val base
      obtain ⟨h,hc,he⟩ := ih s.size (by omega) s rfl good
      have st := (encode_behavior hc).2.1
      rw [he] at st
      have positive : h≠[] ∨ 0 < i := start.imp_left (fun ne hz => ne (he.symm.trans (by rw [hz]; rfl)))
      refine ⟨i::h,Core.step hc positive (by simpa [← st] using allow),?_⟩
      change (encode h).record i=t
      rw [he,recorded]

abbrev AtWeight (k : ℕ) := {t : MarkedPartition // t.Valid ∧ t.weight=k}

noncomputable def partitionEquiv (k : ℕ) : Cores k ≃ AtWeight k := by
  let f : Cores k → AtWeight k := fun ⟨h,hc,hk⟩ =>
    ⟨encode h,(encode_behavior hc).1,(encode_behavior hc).2.2.1.trans hk⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y he
    exact Subtype.ext (encode_injective x.2.1 y.2.1 (congrArg (fun t : AtWeight k => t.val) he))
  · rintro ⟨t,v,wt⟩
    obtain ⟨h,hc,he⟩ := encode_surjective t v
    have hk : h.sum=k := (encode_behavior hc).2.2.1.symm.trans (he ▸ wt)
    exact ⟨⟨h,hc,hk⟩,Subtype.ext he⟩

instance (k : ℕ) : Finite (AtWeight k) := Finite.of_equiv _ (partitionEquiv k)

/-- CLUV Problem 8.3, coefficient by coefficient on the classical source permutations.
The right side counts ordinary partitions, marked levels and strictly increasing weights. -/
theorem stable_1243_partition_formula (n k : ℕ) (large : k+2≤n) :
    sourceCount n k = Nat.card (AtWeight k) :=
  (sourceCount_stable n k large).trans (Nat.card_congr (partitionEquiv k))

end MarkedPartition
end StableInversions
