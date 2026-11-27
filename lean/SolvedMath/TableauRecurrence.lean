import SolvedMath.TableauWords
import SolvedMath.FiniteWordRecurrence
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace PeriodicTableaux

open FiniteWordRecurrence

def diagramEquiv {n} (p q : Heights n) : Diagram p q ≃ Σ i : Bond n, Set.Ioc (p i) (q i) where
  toFun a := ⟨a.1.1,a.1.2,lt_of_not_ge a.2.1,a.2.2⟩
  invFun a := ⟨(a.1,a.2.1),not_le.mpr a.2.2.1,a.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_diagram {n} {p q : Heights n} (hle : p ≤ q) :
    (Nat.card (Diagram p q) : ℤ) = volume p q := by
  rw [Nat.card_congr (diagramEquiv p q),Nat.card_sigma,Nat.cast_sum]
  unfold volume
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.card_eq_fintype_card,Int.card_fintype_Ioc_of_le _ _ (hle i)]

theorem card_translate {n} {p q : Heights n} (hle : p ≤ q) (k : ℕ) :
    Nat.card (Diagram p (translate q k)) = (n+1)*k + Nat.card (Diagram p q) := by
  have hk : p ≤ translate q k := fun i => (hle i).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have term (i : Bond n) : (translate q k) i - p i = (q i - p i) + k := by
    unfold translate
    omega
  apply Int.ofNat_inj.mp
  rw [Nat.cast_add,Nat.cast_mul,card_diagram hk,card_diagram hle]
  simp [volume,term,Finset.sum_add_distrib,add_comm]

def extra {n} : List (Mark n) → ℕ
  | [] => 0
  | (true,_)::ops => extra ops
  | (false,_)::ops => extra ops+1

theorem fresh_add_extra {n} (ops : List (Mark n)) : freshCount ops + extra ops = ops.length := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    obtain ⟨b,i⟩ := op
    cases b <;> simp [extra,freshCount] at * <;> omega

abbrev CountState (n b : ℕ) := Option (State n) × Fin (b+2)

def cap (b v : ℕ) : Fin (b+2) := ⟨min v (b+1),Nat.lt_succ_of_le (min_le_right ..)⟩

def countedStep {n b} (v : CountState n b) (a : Mark n) : CountState n b :=
  (v.1.bind (fun s => step s a),if a.1 then v.2 else cap b (v.2.val+1))

def startState {n} (p : Heights n) (b : ℕ) : CountState n b := (some (state p p),cap b 0)

theorem follow_counted {n} (p : Heights n) (b : ℕ) (ops : List (Mark n)) :
    follow countedStep (startState p b) ops = (run (state p p) ops,cap b (extra ops)) := by
  induction ops with
  | nil => rfl
  | cons op ops ih =>
    change countedStep (follow countedStep (startState p b) ops) op = _
    rw [ih]
    obtain ⟨fresh,i⟩ := op
    cases fresh
    · apply Prod.ext
      · rfl
      · apply Fin.ext
        change min (min (extra ops) (b+1)+1) (b+1) = min (extra ops+1) (b+1)
        omega
    · rfl

def Accept {n b} (y : Outline n) (v : CountState n b) : Prop :=
  (∃ s, v.1=some s ∧ s.1=y) ∧ v.2.val=b

theorem accept_iff {n b} {p q : Heights n} (hle : p≤q) (ops : List (Mark n))
    (hlen : ops.length = Nat.card (Diagram p q)+b) :
    Accept (outline q) (follow countedStep (startState p b) ops) ↔
      (freshCount ops : ℤ) = volume p q ∧ ∃ s, run (state p p) ops=some s ∧ s.1=outline q := by
  rw [follow_counted,← card_diagram hle]
  have total := fresh_add_extra ops
  simp only [Accept,cap,Nat.cast_inj]
  constructor
  · rintro ⟨h,hb⟩
    exact ⟨by omega,h⟩
  · rintro ⟨hc,h⟩
    exact ⟨h,by omega⟩

abbrev Accepted {n} (p : Heights n) (y : Outline n) (b N : ℕ) :=
  {f : Fin N → Mark n // Accept y (follow countedStep (startState p b) (List.ofFn f).reverse)}

noncomputable def pathsEquivAccepted {n b} {p q : Heights n} (hle : p≤q) :
    let N := Nat.card (Diagram p q)+b
    Paths p q N ≃ Accepted p (outline q) b N := by
  let N := Nat.card (Diagram p q)+b
  change Paths p q N ≃ Accepted p (outline q) b N
  refine
    { toFun := fun ops => ⟨(timeList N).symm ⟨ops.1,ops.2.1⟩,?_⟩
      invFun := fun f => ⟨((timeList N) f.1).1,((timeList N) f.1).2,?_⟩
      left_inv := fun ops => ?_
      right_inv := fun f => ?_ }
  · change Accept _ (follow _ _ (((timeList N) ((timeList N).symm ⟨ops.1,ops.2.1⟩)).1))
    rw [Equiv.apply_symm_apply]
    exact (accept_iff hle ops.1 ops.2.1).mpr ops.2.2
  · exact (accept_iff hle _ ((timeList N) f.1).2).mp f.2
  · apply Subtype.ext
    exact congrArg (fun l : {l : List (Mark n) // l.length=N} => l.1)
      ((timeList N).apply_symm_apply ⟨ops.1,ops.2.1⟩)
  · exact Subtype.ext ((timeList N).symm_apply_apply f.1)

noncomputable def wordCount {n} (p q : Heights n) (b : ℕ) : ℕ :=
  Nat.card (SourceWord p q (Nat.card (Diagram p q)+b))

noncomputable def score {n b} (y : Outline n) (v : CountState n b) : ℚ := by
  classical exact if Accept y v then 1 else 0

theorem wordCount_eq_sum {n} {p q : Heights n} (hp : Profile p) (hq : Profile q)
    (hle : p≤q) (b : ℕ) :
    (wordCount p q b : ℚ) =
      ∑ f : Fin (Nat.card (Diagram p q)+b) → Mark n,
        score (outline q) (follow countedStep (startState p b) (List.ofFn f).reverse) := by
  classical
  unfold wordCount
  rw [Nat.card_congr ((sourceEquivPaths hp hq hle).trans (pathsEquivAccepted hle))]
  simp [Accepted,Nat.card_eq_fintype_card,Fintype.card_subtype,score]

/-- One rational constant-coefficient recurrence per width and fixed excess works for every
pair of compatible initial and terminal profiles, including periodic shifts of every zigzag. -/
theorem fixed_excess_recurrence (n b : ℕ) :
    ∃ E : LinearRecurrence ℚ, ∀ (p q : Heights n), Profile p → Profile q → p≤q →
      E.IsSolution (fun k : ℕ => (wordCount p (translate q (k : ℤ)) b : ℚ)) := by
  obtain ⟨E,hE⟩ := periodic_recurrence (countedStep (n := n) (b := b)) (n+1)
  refine ⟨E,fun p q hp hq hle => ?_⟩
  have term (k : ℕ) : (wordCount p (translate q (k : ℤ)) b : ℚ) =
      ∑ f : Fin ((n+1)*k+(Nat.card (Diagram p q)+b)) → Mark n,
        score (outline q) (follow countedStep (startState p b) (List.ofFn f).reverse) := by
    have hk : p ≤ translate q (k : ℤ) :=
      fun i => (hle i).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
    rw [wordCount_eq_sum hp ((profile_translate q _).mpr hq) hk,outline_translate]
    exact congrArg (fun N : ℕ => ∑ f : Fin N → Mark n, score (outline q)
      (follow countedStep (startState p b) (List.ofFn f).reverse))
      (by rw [card_translate hle k,Nat.add_assoc])
  simpa only [term] using hE (score (outline q)) (startState p b) (Nat.card (Diagram p q)+b)


/-- Source statement for k copies of an arbitrary zigzag and exactly b extra labels. -/
theorem dal_zovo_zigzag_recurrence (n b : ℕ) :
    ∃ E : LinearRecurrence ℚ, ∀ p : Heights n, Profile p →
      E.IsSolution (fun k : ℕ => (Nat.card (SourceWord p (translate p k) ((n+1)*k+b)) : ℚ)) := by
  obtain ⟨E,hE⟩ := fixed_excess_recurrence n b
  refine ⟨E, fun p hp => ?_⟩
  have zero : Nat.card (Diagram p p) = 0 := by
    have h := card_diagram (le_refl p)
    simpa [volume] using h
  simpa only [wordCount, card_translate (le_refl p), zero, Nat.add_zero] using
    hE p p hp hp (le_refl _)

end PeriodicTableaux
