module

public import SolvedMath.FoldedSlope

@[expose] public section

namespace FoldedLinearForests

open SimpleGraph BipartiteInducedIsomorphism Set

/-- Variables are binary strings, literals are a variable and its required truth value. -/
abbrev Formula := List (List (List Bool × Bool))

def Satisfiable (F : Formula) : Prop :=
  ∃ assignment : List Bool → Bool, ∀ clause ∈ F, ∃ lit ∈ clause, assignment lit.1 = lit.2

/-- A cons tag precedes every element and a nil tag terminates the list. -/
def listCode {A : Type} (encode : A → List Bool) : List A → List Bool
  | [] => [false]
  | a :: as => true :: (encode a ++ listCode encode as)

def formulaCode : Formula → List Bool :=
  listCode (listCode (fun lit => lit.2 :: listCode (fun b => [b]) lit.1))

/-- Finite transition tables with a state count, a tape alphabet size and a clock exponent.
    An action is either a binary direction or a new symbol. -/
abbrev Table (states symbols : ℕ) :=
  Fin (states+1) → Fin (symbols+3) → Option (Fin (states+1) × (Bool ⊕ Fin (symbols+3)))

abbrev Program := Σ dims : ℕ × ℕ × ℕ, Table dims.1 dims.2.1

def machine {s k : ℕ} (table : Table s k) :
    Turing.TM0.Machine (Fin (k+3)) (Fin (s+1)) := fun q x =>
  (table q x).map fun (state,action) => (state, match action with
    | .inl false => .move .left
    | .inl true => .move .right
    | .inr symbol => .write symbol)

/-- The halted tape contains the self-delimiting pattern code followed by the host code. -/
def Outputs (p : Program) (F : Formula) (H G : ListedGraph) : Prop :=
  let input := formulaCode F
  let k := p.1.2.1
  let M := machine p.2
  let start : Turing.TM0.Cfg (Fin (k+3)) (Fin (p.1.1+1)) :=
    Turing.TM0.init (input.map (inputSymbol k))
  ∃ t ≤ (input.length + 2)^p.1.2.2, ∃ stop,
    (fun state => state.bind (Turing.TM0.step M))^[t] (some start) = some stop ∧
    Turing.TM0.step M stop = none ∧
    stop.Tape.right₀ = Turing.ListBlank.mk ((graphCode H ++ graphCode G).map (inputSymbol k))

/-- SAT reduces to induced embedding with a promised host on every input. -/
def Hard (C : Set ListedGraph) : Prop :=
  ∃ p : Program,
    (∀ F, ∃ H G, Outputs p F H G) ∧
    ∀ F H G, Outputs p F H G → G ∈ C ∧ (Satisfiable F ↔ Nonempty (H.graph ↪g G.graph))

def Hereditary (C : Set ListedGraph) : Prop :=
  ∀ ⦃H G⦄, G ∈ C → Nonempty (H.graph ↪g G.graph) → H ∈ C

def MinimalHard (C : Set ListedGraph) : Prop :=
  Hereditary C ∧ Hard C ∧ ∀ D, D ⊆ C → Hereditary D → Hard D → C ⊆ D

def hostHull (p : Program) : Set ListedGraph :=
  {J | ∃ F H G, Outputs p F H G ∧ Nonempty (J.graph ↪g G.graph)}

private theorem hull_hereditary (p : Program) : Hereditary (hostHull p) := by
  rintro H G ⟨F,P,Q,hr,⟨e⟩⟩ ⟨f⟩
  exact ⟨F,P,Q,hr,⟨f.trans e⟩⟩

theorem minimal_eq_hostHull {C : Set ListedGraph} (h : MinimalHard C) :
    ∃ p, C = hostHull p := by
  obtain ⟨her,⟨p,total,correct⟩,minimal⟩ := h
  have sub : hostHull p ⊆ C := by
    rintro J ⟨F,H,G,hr,emb⟩
    exact her (correct F H G hr).1 emb
  have hard : Hard (hostHull p) := by
    refine ⟨p,total,?_⟩
    intro F H G hr
    exact ⟨⟨F,H,G,hr,⟨RelEmbedding.refl _⟩⟩,(correct F H G hr).2⟩
  exact ⟨p, Set.Subset.antisymm (minimal _ sub (hull_hereditary p) hard) sub⟩

theorem countable_minimal_hard : {C : Set ListedGraph | MinimalHard C}.Countable := by
  apply (Set.countable_range hostHull).mono
  intro C h
  obtain ⟨p,rfl⟩ := minimal_eq_hostHull h
  exact Set.mem_range_self p

/-- The journal's universal Conjecture 3, for a finite alphabet, an almost periodic word
    and a symmetric letter graph that may have loops. The input pattern is unrestricted. -/
def JournalConjecture3 : Prop :=
  ∀ (A : Type) [Fintype A] (w : ℕ → A) (K : LetterGraph A),
    AlmostPeriodic w → MinimalHard (foldedClass w K)

/-- There is an irrational binary rotation word whose fold fails minimal NP-hardness. -/
theorem exists_counterexample_slope :
    ∃ a : ℝ, 1/3 < a ∧ a < 2/3 ∧ Irrational a ∧ ¬ MinimalHard (slopeClass a) := by
  by_contra! all
  let I := Ioo (1/3 : ℝ) (2/3)
  let S := I ∩ {a : ℝ | Irrational a}
  have maps : MapsTo slopeClass S {C : Set ListedGraph | MinimalHard C} := by
    intro a ha
    exact all a ha.1.1 ha.1.2 ha.2
  have inj : InjOn slopeClass S := by
    intro a ha b hb h
    exact slope_eq_of_subclass ha.1.1 ha.1.2 hb.1.1 hb.1.2 h.subset
  have hc := maps.countable_of_injOn inj countable_minimal_hard
  have hI : I.Countable := (hc.union (Set.countable_range (fun r : ℚ => (r : ℝ)))).mono (by
    intro a ha
    by_cases irr : Irrational a
    · exact Or.inl ⟨ha,irr⟩
    · exact Or.inr (Classical.not_not.mp irr))
  have := Cardinal.Real.Ioo_countable_iff.mp hI
  norm_num at this

/-- Counterexample to Alecu–Lozin–Malyshev's Conjecture 3 in its journal formulation. -/
theorem journal_conjecture_three_false : ¬ JournalConjecture3 := by
  intro h
  obtain ⟨a,_,_,ha,hn⟩ := exists_counterexample_slope
  exact hn (h Bool (letter a) onesLoop (mechanical_almostPeriodic ha))

end FoldedLinearForests
