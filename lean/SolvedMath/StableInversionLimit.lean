module

public import SolvedMath.StableInversionHistories

@[expose] public section

namespace StableInversions

/-- A length-free insertion history after stripping the initial identity. -/
inductive Core : List ℕ → Prop
  | nil : Core []
  | step {h : List ℕ} {i : ℕ} (prior : Core h) (starts : h ≠ [] ∨ 0 < i)
      (allowed : (state h).1 ≤ i) : Core (i::h)

@[simp] theorem state_zeros (t : ℕ) : state (List.replicate t 0) = (0,0) := by
  induction t with
  | zero => rfl
  | succ t ih => simp [List.replicate_succ, state, ih, nextState]

@[simp] theorem state_pad (c : List ℕ) (t : ℕ) : state (c ++ List.replicate t 0) = state c := by
  induction c with
  | nil => simp [state]
  | cons i c ih => simp [state,ih]

theorem core_zero_control {c : List ℕ} (hc : Core c) :
    c.count 0 ≤ 1 ∧ (c≠[] → 0 < (state c).2) ∧ (0 < c.count 0 → 0 < (state c).1) := by
  induction hc with
  | nil => simp
  | @step h i hp starts ok ih =>
    obtain ⟨count, bpos, apos⟩ := ih
    by_cases z : i=0
    · subst i
      have ne : h≠[] := starts.resolve_right (by omega)
      have b := bpos ne
      have zero : h.count 0 = 0 := by by_contra! hz; have := apos (by omega); omega
      simp [state, nextState, b, zero]
    · have pi : 0 < i := by omega
      have hi : (i==0)=false := by simpa using z
      simp only [List.count_cons, hi, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, state]
      unfold nextState
      split <;> simp_all

theorem length_le_weight (h : List ℕ) : h.length ≤ h.sum+h.count 0 := by
  induction h with
  | nil => simp
  | cons a h ih => by_cases ha : a=0 <;> simp_all <;> omega

theorem member_budget (h : List ℕ) (i : ℕ) (mem : i∈h) : h.length+i ≤ h.sum+h.count 0+1 := by
  induction h with
  | nil => simp at mem
  | cons a h ih =>
    rcases List.mem_cons.1 mem with eq | inside
    · subst a
      have := length_le_weight h
      by_cases hi : i=0 <;> simp [hi] <;> omega
    · have := ih inside
      by_cases ha : a=0 <;> simp [ha] <;> omega

private theorem admissible_zeros (t : ℕ) : admissible (List.replicate t 0) := by
  induction t with
  | zero => trivial
  | succ t ih => simp [List.replicate_succ, admissible, ih]

theorem admissible_pad {c : List ℕ} (hc : Core c) (t : ℕ) (bounds : ∀ i∈c, i≤t) :
    admissible (c++List.replicate t 0) := by
  induction hc with
  | nil => exact admissible_zeros t
  | @step h i hp _ ok ih =>
    refine ⟨ih (fun a ha => bounds a (by simp [ha])), by simpa using ok, ?_⟩
    have := bounds i (by simp)
    simp; omega

def trim : List ℕ → List ℕ
  | [] => []
  | i::h => if trim h=[] ∧ i=0 then [] else i::trim h

@[simp] theorem trim_zeros (t : ℕ) : trim (List.replicate t 0) = [] := by
  induction t with
  | zero => rfl
  | succ t ih => simp [List.replicate_succ, trim, ih]

@[simp] theorem trim_pad (c : List ℕ) (t : ℕ) : trim (c++List.replicate t 0) = trim c := by
  induction c with
  | nil => simp [trim]
  | cons i c ih => simp [trim,ih]

theorem trim_core {c : List ℕ} (hc : Core c) : trim c=c := by
  induction hc with
  | nil => rfl
  | @step h i _ starts _ ih =>
    have hni : ¬ (h=[] ∧ i=0) := by rintro ⟨rfl,rfl⟩; simp at starts
    simp [trim,ih,hni]

theorem unique_padding {h : List ℕ} (ok : admissible h) : ∃ c t, Core c ∧ h=c++List.replicate t 0 := by
  induction h with
  | nil => exact ⟨[],0,.nil,rfl⟩
  | cons i h ih =>
    obtain ⟨old,slot,_⟩ := ok
    obtain ⟨c,t,hc,rfl⟩ := ih old
    by_cases base : c=[] ∧ i=0
    · obtain ⟨rfl,rfl⟩ := base
      exact ⟨[],t+1,.nil, by simp [List.replicate_succ]⟩
    · have starts : c ≠ [] ∨ 0 < i := by
        by_cases he : c=[]
        · exact Or.inr (by by_contra! hz; exact base ⟨he,by omega⟩)
        · exact Or.inl he
      exact ⟨i::c,t,.step hc starts (by simpa using slot),rfl⟩

abbrev Cores (k : ℕ) := {c : List ℕ // Core c ∧ c.sum=k}

/-- At every n ≥ k+2, padding a reduced history is a genuine bijection at inversion count k. -/
noncomputable def paddingEquiv (n k : ℕ) (large : k+2≤n) : Cores k ≃ Histories n k := by
  let f : Cores k → Histories n k := fun ⟨c,hc,hk⟩ => by
    have cnt := (core_zero_control hc).1
    have len := length_le_weight c
    have bounds (i : ℕ) (mem : i∈c) : i≤n-c.length := by have := member_budget c i mem; omega
    refine ⟨c++List.replicate (n-c.length) 0,admissible_pad hc _ bounds,?_,?_⟩
    · simp; omega
    · simp [hk]
  apply Equiv.ofBijective f
  constructor
  · intro x y eq
    apply Subtype.ext
    have he := congrArg (fun d : Histories n k => trim d.val) eq
    change trim (x.val++List.replicate (n-x.val.length) 0) = trim (y.val++List.replicate (n-y.val.length) 0) at he
    simpa [trim_core x.2.1, trim_core y.2.1] using he
  · rintro ⟨h,hl,hn,hk⟩
    obtain ⟨c,t,hc,rfl⟩ := unique_padding hl
    simp only [List.length_append, List.length_replicate] at hn
    have key : n-c.length=t := by omega
    refine ⟨⟨c,hc,by simpa using hk⟩,Subtype.ext ?_⟩
    change c++List.replicate (n-c.length) 0=c++List.replicate t 0
    rw [key]

instance (k : ℕ) : Finite (Cores k) := Finite.of_equiv _ (paddingEquiv (k+2) k le_rfl).symm

theorem sourceCount_stable (n k : ℕ) (large : k+2≤n) : sourceCount n k = Nat.card (Cores k) :=
  (sourceCount_eq_histories n k).trans (Nat.card_congr (paddingEquiv n k large).symm)

end StableInversions
