# Lean status

The project uses Lean 4.36.0. The cluster-height and periodic-tableau developments use pinned Mathlib. All coordinates in the separator formalization are zero-based. The explicit overlap-two theorem accepts the authors’ one-based endpoint inequalities. The general classification accepts the prefix–suffix order equivalence in the paper.

| Result | Checked statement |
|---|---|
| Lee–Sah cluster heights | `LeeSah.lee_sah_conjecture61` proves the 2018 conjecture with all endpoint choices, all marked positions and the original uniform extension counts. `LeeSah.extension_rank_tail_all` gives positive constants for a uniform exponential bound at every stack size. [Final Lean theorems](../lean/SolvedMath/ClusterLimit.lean) · [Figure 3 normalization](../lean/SolvedMath/ClusterFigure.lean) · [Rank transfer](../lean/SolvedMath/ClusterExtensionLaw.lean) · [Spine law](../lean/SolvedMath/ClusterSpineLaw.lean) · [Review](../results/lee-sah-cluster-height/AUDIT.md) |
| Distinct patterns in a random permutation | `normalizedMean_by_occurrences` expresses the exact source quantity by embedding classes, and `local_swap_pattern` verifies the pointwise move. `source_limit_from_embedding_estimates` derives the exact mean limit from binomial moment convergence and class localization. Those two estimates and the distribution and variance are proved in writing. [Finite Lean model](../lean/SolvedMath/RandomPatternClasses.lean) · [Analytic implication](../lean/SolvedMath/RandomPatternMoments.lean) · [Review](../results/distinct-random-permutation-patterns/AUDIT.md) |
| Periodic set-valued tableaux | `PeriodicTableaux.sourceEquivPaths` identifies the source surjections with finite-state paths. `wordCount_eq_sum` counts all excesses, and `fixed_excess_recurrence` proves the common recurrence for every growing pair of profiles, and `dal_zovo_zigzag_recurrence` specializes it to the source’s periodic zigzags. `StripCoordinates.printed_no_eventual_recurrence` rules out every complex recurrence in the literal strip coordinates. The asymptotic estimates have written proofs. [Recurrence](../lean/SolvedMath/TableauRecurrence.lean) · [Literal version](../lean/SolvedMath/StripCoordinates.lean) · [Audit](../results/periodic-set-valued-tableaux/AUDIT.md) |
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
