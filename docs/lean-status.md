# Lean status

The project uses Lean 4.36.0. The cluster-height development also uses pinned Mathlib. All coordinates in the separator formalization are zero-based. The explicit overlap-two theorem accepts the authors’ one-based endpoint inequalities. The general classification accepts the prefix–suffix order equivalence in the paper.

| Result | Checked statement |
|---|---|
| Lee–Sah cluster heights | `LeeSah.density_sandwich` proves the all-window comparison. `LeeSah.tilt_bound` controls the normalization, `LeeSah.uniform_cube_tail` proves the simultaneous concentration of a uniform sample, and `LeeSah.conjecture61_of_tail_bound` deduces the original convergence from exponential concentration of the actual ranks. That probability estimate has a reviewed written proof and remains open in the formalization. [Lean source](../lean/SolvedMath/ClusterHeight.lean) · [Review](../results/lee-sah-cluster-height/AUDIT.md) |
| Pattern-poset separators | `SolvedMath.PatternSeparator.bks_overlap_two_separator` proves the paper’s proposed family, including both nonchain conditions. `SolvedMath.PatternSeparator.SeparatedOverlap.separator` proves the shared-gap sufficient condition. [Source](../lean/SolvedMath/PatternSeparator.lean) |
| General separator classification | `SolvedMath.PatternSeparator.bks_separator_at` decides the source poset at any specified occurrence count. `SolvedMath.PatternSeparator.bks_separator_always` decides the universally quantified condition. Both results apply to every compatible overlap. [Lean source](../lean/SolvedMath/SeparatorClassification.lean) · [Independent type-checker record](../results/pattern-poset-separator/CLASSIFICATION-AUDIT.md) |

The archived manuscripts have written proofs and exact Python checks. [Big-descent audit](../archive/big-descents/AUDIT.md) · [Packing-cutoff audit](../archive/packing-cutoff/AUDIT.md)

The axiom audit checks the kernel’s dependency reports for all registered declarations. The explicit separator, the shared-gap theorem, and the physical reachability and asymmetry lemmas use only propositional extensionality (`propext`) and quotient soundness (`Quot.sound`). The two general decision theorems also use `Classical.choice`. Adding a placeholder or a project-specific axiom to their dependency chain fails the audit. [Audit source](../lean/ProofAudit.lean)

To rerun the Lean portion from the repository root, use

```sh
cd lean
lake build
lake env leanchecker --fresh --verbose SolvedMath
```
