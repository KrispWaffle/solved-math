import SolvedMath.TableauProfiles

namespace PeriodicTableaux

/-- Offsets from the first diagonal, bounded solely by the strip width. -/
abbrev Outline (n : ℕ) := Bond n → Bond n
abbrev State (n : ℕ) := Outline n × Finset (Bond n)

def outline {n} (h : Heights n) : Outline n := fun i =>
  ⟨min (h 0-h i).toNat n, Nat.lt_succ_of_le (min_le_right ..)⟩

def base {n} (x : Outline n) : Heights n := fun i => -(x i : ℤ)
def translate {n} (h : Heights n) (c : ℤ) : Heights n := fun i => h i + c

def visited {n} (p h : Heights n) : Finset (Bond n) := Finset.univ.filter fun i => p i < h i
def state {n} (p h : Heights n) : State n := (outline h,visited p h)

theorem base_outline {n} {h : Heights n} (hh : Profile h) :
    base (outline h) = translate h (-(h 0)) := by
  funext i
  obtain ⟨h₁,h₂⟩ := hh 0 i (Fin.zero_le _)
  have a : h 0 - h i ≥ 0 := by omega
  have b : (h 0-h i).toNat ≤ n := by
    have hi := i.isLt
    simp only [Fin.val_zero, Nat.cast_zero, add_zero] at h₂
    omega
  simp [base,outline,translate,min_eq_left b,Int.toNat_of_nonneg a]
  omega

@[simp] theorem outline_translate {n} (h : Heights n) (c : ℤ) :
    outline (translate h c) = outline h := by ext i; simp [outline,translate]

@[simp] theorem profile_translate {n} (h : Heights n) (c : ℤ) :
    Profile (translate h c) ↔ Profile h := by
  unfold Profile translate
  constructor <;> intro H i j hij <;> specialize H i j hij <;> constructor <;> omega

@[simp] theorem raise_translate {n} (h : Heights n) (c : ℤ) (i : Bond n) :
    raise (translate h c) i = translate (raise h i) c := by
  funext j
  by_cases he : j = i <;> simp [raise,Function.update,translate,he]
  omega

@[simp] theorem lower_translate {n} (h : Heights n) (c : ℤ) (i : Bond n) :
    lower (translate h c) i = translate (lower h i) c := by
  funext j
  by_cases he : j = i <;> simp [lower,Function.update,translate,he]
  omega

@[simp] theorem visited_initial {n} (p : Heights n) : visited p p = ∅ := by simp [visited]

theorem visited_raise {n} {p h : Heights n} (hle : p ≤ h) (i : Bond n) :
    visited p (raise h i) = insert i (visited p h) := by
  ext j
  by_cases he : j = i
  · subst j
    have hi : p i ≤ h i := hle i
    simp [visited]
    omega
  · simp [visited,raise,Function.update,he]

instance {n} (h : Heights n) : Decidable (Profile h) := by unfold Profile; infer_instance

/-- A failed step has no transition. Each successful mark records which physical bond was used. -/
def step {n} (s : State n) : Mark n → Option (State n)
  | (true,i) =>
    if Profile (raise (base s.1) i) then some (outline (raise (base s.1) i),insert i s.2)
    else none
  | (false,i) =>
    if i ∈ s.2 ∧ Profile (lower (base s.1) i) then some s else none

theorem step_discover {n} {p h : Heights n} (hh : Profile h) (hle : p ≤ h) (i : Bond n) :
    step (state p h) (true,i) =
      if Profile (raise h i) then some (state p (raise h i)) else none := by
  simp [step,state,base_outline hh,visited_raise hle]

theorem step_repeat {n} {p h : Heights n} (hh : Profile h) (i : Bond n) :
    step (state p h) (false,i) =
      if p i < h i ∧ Profile (lower h i) then some (state p h) else none := by
  simp [step,state,base_outline hh,visited]

def run {n} (start : State n) : List (Mark n) → Option (State n)
  | [] => some start
  | op::ops => (run start ops).bind fun s => step s op

theorem Trace.run_eq {n} {p h : Heights n} {ops l} (hp : Profile p) (t : Trace p h ops l) :
    run (state p p) ops = some (state p h) := by
  induction t with
  | nil => rfl
  | discover t i en ih => simp [run,ih,step_discover (t.sound hp).1 (t.sound hp).2.1,en]
  | repeatCell t i hi hl ih => simp [run,ih,step_repeat (t.sound hp).1,hi,hl]

theorem trace_of_run {n} {p : Heights n} (hp : Profile p) (ops : List (Mark n)) {s : State n}
    (hr : run (state p p) ops = some s) :
    Trace p (finalH p ops) ops (readCells p ops) ∧ state p (finalH p ops) = s := by
  induction ops generalizing s with
  | nil =>
    exact ⟨Trace.nil,Option.some.inj hr⟩
  | cons op ops ih =>
    obtain ⟨b,i⟩ := op
    cases prev : run (state p p) ops with
    | none => simp [run,prev] at hr
    | some v =>
      obtain ⟨t,hv⟩ := ih prev
      subst v
      have hh := t.sound hp
      cases b
      · simp only [run,prev,Option.bind_some,step_repeat hh.1] at hr
        split at hr
        · rename_i ok
          exact ⟨Trace.repeatCell t i ok.1 ok.2,Option.some.inj hr⟩
        · contradiction
      · simp only [run,prev,Option.bind_some,step_discover hh.1 hh.2.1] at hr
        split at hr
        · rename_i ok
          exact ⟨Trace.discover t i ok,Option.some.inj hr⟩
        · contradiction

theorem profile_ext {n} {p h q : Heights n} (hh : Profile h) (hq : Profile q)
    (ho : outline h = outline q) (hv : volume p h = volume p q) : h=q := by
  have be := congrArg base ho
  rw [base_outline hh,base_outline hq] at be
  have hi (i : Bond n) : h i - p i = (q i - p i) + (h 0-q 0) := by
    have he := congrFun be i
    dsimp [translate] at he
    omega
  have he : volume p h = volume p q + (n+1 : ℕ) * (h 0-q 0) := by
    simp [volume,hi,Finset.sum_add_distrib,mul_sub]
  have hz : h 0 - q 0 = 0 := by
    have prod : ((n+1 : ℕ) : ℤ) * (h 0-q 0) = 0 := by omega
    exact (mul_eq_zero.mp prod).resolve_left (by positivity)
  funext i
  have := hi i
  omega

abbrev Words {n} (p q : Heights n) (N : ℕ) :=
  {l : List (Cell n) // l.length=N ∧ History p q l}

abbrev Paths {n} (p q : Heights n) (N : ℕ) :=
  {ops : List (Mark n) // ops.length=N ∧ (freshCount ops : ℤ)=volume p q ∧
    ∃ s, run (state p p) ops=some s ∧ s.1=outline q}

/-- Counts the source's surjective, order-compatible words by walks on a width-bounded state space. -/
def wordsEquivPaths {n} {p q : Heights n} (hp : Profile p) (hq : Profile q) (hle : p≤q) (N : ℕ) :
    Words p q N ≃ Paths p q N where
  toFun l := by
    have t := trace_of_history hp l.1 q hq hle l.2.2
    exact ⟨tags l.1,by simpa using l.2.1,by rw [← volume_final p,t.final_eq],
      state p q,t.run_eq hp,rfl⟩
  invFun ops := by
    refine ⟨readCells p ops.1,by simpa using ops.2.1,?_⟩
    obtain ⟨s,hr,ho⟩ := ops.2.2.2
    have t := trace_of_run hp ops.1 hr
    have he := profile_ext (t.1.sound hp).1 hq ((congrArg Prod.fst t.2).trans ho)
      ((volume_final p ops.1).trans ops.2.2.1)
    exact (congrArg (fun h => History p h (readCells p ops.1)) he).mp (t.1.sound hp).2.2
  left_inv l := Subtype.ext (trace_of_history hp l.1 q hq hle l.2.2).cells_eq
  right_inv ops := by
    obtain ⟨s,hr,_⟩ := ops.2.2.2
    exact Subtype.ext ((trace_of_run hp ops.1 hr).1.tags_eq hp)

end PeriodicTableaux
