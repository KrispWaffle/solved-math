module

public import SolvedMath.TwoCenterPacking
public import Mathlib.Computability.TuringMachine.PostTuringMachine

@[expose] public section

namespace BipartiteInducedIsomorphism

open SimpleGraph

/-- Two vertex orders represent the graph if disagreement of the orders is exactly adjacency. -/
def HasPermutationOrders {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ top bottom : V ↪ ℕ, ∀ u v, G.Adj u v ↔
    (top u < top v ∧ bottom v < bottom u) ∨ (top v < top u ∧ bottom u < bottom v)

def IsBipartitePermutation {V : Type} (G : SimpleGraph V) : Prop :=
  (∃ color : V → Bool, ∀ u v, G.Adj u v → color u ≠ color v) ∧ HasPermutationOrders G

structure ListedGraph where
  n : ℕ
  graph : SimpleGraph (Fin n)

def classAt (k : ℕ) (G : ListedGraph) : Prop :=
  IsBipartitePermutation G.graph ∧ IsEmpty (pathGraph k ↪g G.graph)

/-- A unary order header followed by the entire adjacency matrix in row-major order. -/
noncomputable def graphCode (G : ListedGraph) : List Bool := by
  classical
  exact List.replicate G.n true ++ [false] ++
    (List.finRange G.n).flatMap (fun i => (List.finRange G.n).map (fun j => decide (G.graph.Adj i j)))

def inputSymbol (e : ℕ) (b : Bool) : Fin (e+3) :=
  ⟨if b then 2 else 1, by cases b <;> simp⟩

/-- A polynomial-time deterministic decision algorithm for any pattern in a host from the class.
    The blank symbol is zero. Two other symbols encode the bits, and each graph code is
    self-delimiting. Finite states and tape alphabets may depend on the class. -/
def PolynomialISI (C : ListedGraph → Prop) : Prop :=
  ∃ states symbols degree : ℕ,
    ∃ M : Turing.TM0.Machine (Fin (symbols+3)) (Fin (states+1)),
    ∃ accepts : Fin (states+1) → Bool,
      ∀ H G, C G →
        let input := graphCode H ++ graphCode G
        let start : Turing.TM0.Cfg (Fin (symbols+3)) (Fin (states+1)) :=
          Turing.TM0.init (input.map (inputSymbol symbols))
        ∃ time ≤ (input.length + 2)^degree, ∃ stop,
          (fun state => state.bind (Turing.TM0.step M))^[time] (some start) = some stop ∧
          Turing.TM0.step M stop = none ∧
          (accepts stop.q = true ↔ Nonempty (H.graph ↪g G.graph))

/-- The path form stated immediately after Alecu–Lozin–Malyshev's Conjecture 2 in §5. -/
def AlecuLozinMalyshevPathForm : Prop := ∀ k : ℕ, 0 < k → PolynomialISI (classAt k)

def initialPath {k l : ℕ} (h : k ≤ l) : pathGraph k ↪g pathGraph l where
  toFun i := i.castLE h
  inj' := fun _ _ eq => Fin.ext (congrArg (fun v : Fin l => v.val) eq)
  map_rel_iff' := Iff.rfl

theorem classAt_monotone {k l} (h : k ≤ l) (G : ListedGraph) :
    classAt k G → classAt l G := by
  rintro ⟨hp,he⟩
  exact ⟨hp, ⟨fun f => he.false ((initialPath h).trans f)⟩⟩

theorem polynomial_on_subclass {C D : ListedGraph → Prop} (sub : ∀ G, C G → D G)
    (h : PolynomialISI D) : PolynomialISI C := by
  obtain ⟨states,symbols,degree,M,accepts,halting⟩ := h
  exact ⟨states,symbols,degree,M,accepts,fun H G hG => halting H G (sub G hG)⟩

/-- The two complexity endpoints imply the decision-time dichotomy at all path lengths. -/
theorem path_dichotomy (five : PolynomialISI (classAt 5))
    (six : ¬ PolynomialISI (classAt 6)) (k : ℕ) :
    PolynomialISI (classAt k) ↔ k ≤ 5 := by
  constructor
  · intro algo
    by_contra hk
    exact six (polynomial_on_subclass (classAt_monotone (by omega : 6 ≤ k)) algo)
  · intro hk
    exact polynomial_on_subclass (classAt_monotone hk) five

theorem path_form_false (six : ¬ PolynomialISI (classAt 6)) : ¬ AlecuLozinMalyshevPathForm :=
  fun h => six (h 6 (by decide))

def width (p : Bool → ℕ) (c : ℕ) := p false + p true + c + 1

/-- Positions in the two explicit orders of the five path parts, using disjoint intervals. -/
def orderRank {p c} (bottom : Bool) : ChairVertex p c → ℕ
  | .inl false => if bottom then 2 * width p c else 0
  | .inl true => if bottom then 4 * width p c else 2 * width p c
  | .inr (.inl j) => (if bottom then 1 else 3) * width p c + j.val
  | .inr (.inr ⟨false,j⟩) => (if bottom then 0 else 1) * width p c + j.val
  | .inr (.inr ⟨true,j⟩) => (if bottom then 3 else 4) * width p c + j.val

theorem orderRank_injective {p c} (b : Bool) : Function.Injective (@orderRank p c b) := by
  intro u v h
  rcases u with (s | (i | ⟨s,i⟩)) <;> try cases s
  all_goals rcases v with (s | (j | ⟨s,j⟩)) <;> try cases s
  all_goals cases b <;> simp_all [orderRank, width, Fin.ext_iff] <;> omega

theorem chair_orders (p : Bool → ℕ) (c : ℕ) : IsBipartitePermutation (chairs p c) := by
  constructor
  · refine ⟨Sum.elim (fun _ => false) (fun _ => true), ?_⟩
    rintro (u | u) (v | v) h
    · exact False.elim h
    · exact Bool.false_ne_true
    · exact Ne.symm Bool.false_ne_true
    · exact False.elim h
  · refine ⟨⟨_,orderRank_injective false⟩,⟨_,orderRank_injective true⟩,?_⟩
    intro u v
    change chairAdj u v ↔
      (orderRank false u < orderRank false v ∧ orderRank true v < orderRank true u) ∨
      (orderRank false v < orderRank false u ∧ orderRank true u < orderRank true v)
    rcases u with (s | (i | ⟨s,i⟩)) <;> try cases s
    all_goals rcases v with (s | (j | ⟨s,j⟩)) <;> try cases s
    all_goals simp [orderRank, width, chairAdj, sees]
    all_goals omega

end BipartiteInducedIsomorphism
