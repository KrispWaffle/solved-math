module

public import SolvedMath.UnitIntervalDensity
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Order.WellFoundedSet

@[expose] public section

namespace UnitIntervalMinors

open Set

theorem higmanWords {α : Type} (r : α → α → Prop) [IsPreorder α r]
    (hr : WellQuasiOrdered r) : WellQuasiOrdered (List.SublistForall₂ r) := by
  have h := Set.PartiallyWellOrderedOn.partiallyWellOrderedOn_sublistForall₂ r
    (Set.partiallyWellOrderedOn_univ_iff.mpr hr)
  simpa only [Set.mem_univ, implies_true, forall_const, Set.ofPred_true,
    Set.partiallyWellOrderedOn_univ_iff] using h

private theorem finite_subwords {α : Type} [Finite α] : WellQuasiOrdered (@List.Sublist α) := by
  have eqw : WellQuasiOrdered (@Eq α) := Finite.wellQuasiOrdered _
  intro seq
  obtain ⟨i,j,lt,h⟩ := higmanWords _ eqw seq
  obtain ⟨l,e,sub⟩ := List.sublistForall₂_iff.mp h
  rw [List.forall₂_eq_eq_eq] at e
  exact ⟨i,j,lt,e ▸ sub⟩

private theorem get_embedding {n m : ℕ} {α : Type} (f : Fin n → α) (g : Fin m → α)
    (sub : (List.ofFn f).Sublist (List.ofFn g)) :
    ∃ e : Fin n ↪o Fin m, ∀ i, f i = g (e i) := by
  obtain ⟨k,hk⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp sub
  let left := Fin.castOrderIso (List.length_ofFn (f := f)).symm
  let right := Fin.castOrderIso (List.length_ofFn (f := g))
  refine ⟨left.toOrderEmbedding.trans (k.trans right.toOrderEmbedding), fun i => ?_⟩
  simpa [left,right,Fin.cast] using hk (left i)

/-- On a fractional-part tie, put the larger integer part first. This convention
    preserves contacts of closed unit intervals even in drawings with coincident endpoints. -/
private noncomputable def key (x : ℝ) : ℝ ×ₗ ℤ := toLex (Int.fract x, -⌊x⌋)

private theorem decode {x y : ℝ} (order : key x ≤ key y) :
    (x ≤ y+1 ∧ y ≤ x+1) ↔ ⌊x⌋ = ⌊y⌋ ∨ ⌊x⌋ = ⌊y⌋+1 := by
  obtain ⟨frac,tie⟩ := Prod.Lex.toLex_le_toLex'.mp order
  change Int.fract x ≤ Int.fract y at frac
  change Int.fract x = Int.fract y → -⌊x⌋ ≤ -⌊y⌋ at tie
  have hx := Int.floor_add_fract x
  have hy := Int.floor_add_fract y
  have bx := Int.fract_nonneg x
  have byy := Int.fract_nonneg y
  have ux := Int.fract_lt_one x
  have uy := Int.fract_lt_one y
  constructor
  · rintro ⟨h₁,h₂⟩
    have lo : ⌊y⌋ ≤ ⌊x⌋ := by
      by_contra! outside
      have up : (⌊x⌋ : ℝ)+1 ≤ (⌊y⌋ : ℝ) := by exact_mod_cast outside
      have hfrac : Int.fract x = Int.fract y := le_antisymm frac (by linarith)
      have ht := tie hfrac
      omega
    have hi : ⌊x⌋ ≤ ⌊y⌋+1 := by
      by_contra! outside
      have two : ⌊y⌋+2 ≤ ⌊x⌋ := by omega
      have up : (⌊y⌋ : ℝ)+2 ≤ (⌊x⌋ : ℝ) := by exact_mod_cast two
      linarith
    omega
  · rintro (same | next)
    · have e : (⌊x⌋ : ℝ) = (⌊y⌋ : ℝ) := by exact_mod_cast same
      constructor <;> linarith
    · have e : (⌊x⌋ : ℝ) = (⌊y⌋ : ℝ)+1 := by exact_mod_cast next
      constructor <;> linarith

/-- Arbitrary finitely labelled unit intervals in a strip of fixed length. -/
structure BoundedDrawing (k : ℕ) (α : Type) where
  size : ℕ
  start : Fin size → ℝ
  lower : ∀ i, 0 ≤ start i
  upper : ∀ i, start i < k
  label : Fin size → α

namespace BoundedDrawing

variable {k : ℕ} {α : Type}

private noncomputable def perm (D : BoundedDrawing k α) := Tuple.sort (key ∘ D.start)

private noncomputable def letter (D : BoundedDrawing k α) (i : Fin D.size) : Fin k × α :=
  (⟨⌊D.start (D.perm i)⌋₊, (Nat.floor_lt (D.lower _)).mpr (D.upper _)⟩,D.label (D.perm i))

private theorem sorted_adj (D : BoundedDrawing k α) {i j : Fin D.size} (ij : i < j) :
    (unitGraph D.start).Adj (D.perm i) (D.perm j) ↔
      (D.letter i).1.val = (D.letter j).1.val ∨ (D.letter i).1.val = (D.letter j).1.val+1 := by
  have hkey : key (D.start (D.perm i)) ≤ key (D.start (D.perm j)) :=
    Tuple.monotone_sort (key ∘ D.start) ij.le
  have ne := D.perm.injective.ne ij.ne
  change (_ ≠ _ ∧ _) ↔ _
  rw [and_iff_right ne, overlap_iff (by linarith) (by linarith),decode hkey]
  have ei := Int.natCast_floor_eq_floor (D.lower (D.perm i))
  have ej := Int.natCast_floor_eq_floor (D.lower (D.perm j))
  rw [←ei,←ej]
  simp only [letter]
  omega

/-- Every infinite sequence of bounded-strip drawings has an earlier graph occurring
    as an induced subgraph of a later one with all vertex labels preserved. -/
theorem wellQuasiOrdered [Finite α] : WellQuasiOrdered
    (fun D E : BoundedDrawing k α => ∃ f : unitGraph D.start ↪g unitGraph E.start,
      ∀ i, D.label i = E.label (f i)) := by
  intro seq
  obtain ⟨i,j,lt,sub⟩ := finite_subwords (fun n => List.ofFn (seq n).letter)
  let D := seq i
  let E := seq j
  obtain ⟨kmap,hk⟩ := get_embedding D.letter E.letter sub
  let f : Fin D.size ↪ Fin E.size := D.perm.symm.toEmbedding.trans
    (kmap.toEmbedding.trans E.perm.toEmbedding)
  have fp (x) : f (D.perm x) = E.perm (kmap x) := by simp [f]
  have before {x y : Fin D.size} (hxy : x < y) :
      (unitGraph E.start).Adj (f (D.perm x)) (f (D.perm y)) ↔
      (unitGraph D.start).Adj (D.perm x) (D.perm y) := by
    rw [fp, fp, E.sorted_adj (kmap.strictMono hxy),D.sorted_adj hxy,hk x,hk y]
  refine ⟨i,j,lt,⟨{ toEmbedding := f, map_rel_iff' := ?_ },?_⟩⟩
  · intro u v
    obtain ⟨x,rfl⟩ := D.perm.surjective u
    obtain ⟨y,rfl⟩ := D.perm.surjective v
    obtain hxy | rfl | hyx := lt_trichotomy x y
    · exact before hxy
    · simp
    · exact ((unitGraph E.start).adj_comm _ _).trans ((before hyx).trans ((unitGraph D.start).adj_comm _ _))
  · intro u
    obtain ⟨x,rfl⟩ := D.perm.surjective u
    change D.label (D.perm x) = E.label (f (D.perm x))
    rw [fp]
    exact congrArg Prod.snd (hk x)

end BoundedDrawing
end UnitIntervalMinors
