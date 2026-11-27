import SolvedMath.TableauMachine
import Mathlib.Data.List.OfFn
import Mathlib.SetTheory.Cardinal.Finite

namespace PeriodicTableaux

/-- A tuple is in chronological order, a history has its newest letter first. -/
def timeList {α : Type*} (N : ℕ) : (Fin N → α) ≃ {l : List α // l.length=N} where
  toFun f := ⟨(List.ofFn f).reverse,by simp⟩
  invFun l i := l.1.reverse.get ⟨i,by simp [l.2]⟩
  left_inv f := by funext i; simp [List.get_eq_getElem]
  right_inv l := by
    apply Subtype.ext
    apply List.reverse_inj.mp
    simp only [List.reverse_reverse]
    apply List.ext_getElem
    · simp [l.2]
    · intro i hi hj
      simp [List.get_eq_getElem]

abbrev Diagram {n} (p q : Heights n) := {a : Cell n // Seen p q a}

/-- Surjective words of physical cells. All occurrences respect strict product comparisons. -/
abbrev SourceWord {n} (p q : Heights n) (N : ℕ) :=
  {f : Fin N → Diagram p q // Function.Surjective f ∧
    ∀ ⦃i j⦄, i < j → ¬Before (f j).1 (f i).1}

def Admissible {n N} (p q : Heights n) (f : Fin N → Cell n) : Prop :=
  (∀ a, (∃ i, f i = a) ↔ Seen p q a) ∧ ∀ ⦃i j⦄, i < j → ¬Before (f j) (f i)

theorem history_timeList {n N} (p q : Heights n) (f : Fin N → Cell n) :
    History p q ((timeList N) f).1 ↔ Admissible p q f := by
  simp [timeList,History,Admissible,List.mem_ofFn,List.pairwise_reverse,List.pairwise_ofFn]

def sourceEquivFunctions {n N} (p q : Heights n) :
    SourceWord p q N ≃ {f : Fin N → Cell n // Admissible p q f} where
  toFun word := by
    refine ⟨fun i => (word.1 i).1,⟨fun a => ⟨?_,?_⟩,word.2.2⟩⟩
    · rintro ⟨i,rfl⟩
      exact (word.1 i).2
    · intro h
      obtain ⟨i,hi⟩ := word.2.1 ⟨a,h⟩
      exact ⟨i,congrArg Subtype.val hi⟩
  invFun word := by
    refine ⟨fun i => ⟨word.1 i,(word.2.1 _).mp ⟨i,rfl⟩⟩,?_,word.2.2⟩
    intro a
    obtain ⟨i,hi⟩ := (word.2.1 a.1).mpr a.2
    exact ⟨i,Subtype.ext hi⟩
  left_inv _ := rfl
  right_inv _ := rfl

def functionsEquivWords {n N} (p q : Heights n) :
    {f : Fin N → Cell n // Admissible p q f} ≃ Words p q N where
  toFun f := ⟨((timeList N) f.1).1,((timeList N) f.1).2,(history_timeList ..).mpr f.2⟩
  invFun l := by
    let v : {l : List (Cell n) // l.length=N} := ⟨l.1,l.2.1⟩
    refine ⟨(timeList N).symm v,(history_timeList ..).mp ?_⟩
    rw [Equiv.apply_symm_apply]
    exact l.2.2
  left_inv f := Subtype.ext ((timeList N).symm_apply_apply f.1)
  right_inv l := by
    apply Subtype.ext
    exact congrArg (fun z : {l : List (Cell n) // l.length=N} => z.1)
      ((timeList N).apply_symm_apply ⟨l.1,l.2.1⟩)

def sourceEquivPaths {n N} {p q : Heights n} (hp : Profile p) (hq : Profile q) (hle : p≤q) :
    SourceWord p q N ≃ Paths p q N :=
  ((sourceEquivFunctions p q).trans (functionsEquivWords p q)).trans (wordsEquivPaths hp hq hle N)

end PeriodicTableaux
