# Lean status

The project uses Lean 4.36.0 and its core library. All coordinates in the separator formalization are zero-based. The source-facing declaration takes the ranks and gap inequalities in the authors’ one-based notation.

| Result | Checked statement |
|---|---|
| Pattern-poset separators | `SolvedMath.PatternSeparator.bks_overlap_two_separator` proves the paper’s proposed family, including both nonchain conditions. `SolvedMath.PatternSeparator.SeparatedOverlap.separator` proves the arbitrary-overlap theorem. [Source](../lean/SolvedMath/PatternSeparator.lean) |
| Big descents | Written proof and Python checker. [Scope](../results/big-descents/AUDIT.md) |
| Packing cutoff | Written proof and Python checker. [Scope](../results/packing-cutoff/AUDIT.md) |

The axiom audit checks the kernel’s dependency reports for both separator declarations. Each uses only propositional extensionality (`propext`) and quotient soundness (`Quot.sound`). Adding a placeholder or a project-specific axiom to their dependency chain fails the audit. [Audit source](../lean/ProofAudit.lean)

To rerun the Lean portion from the repository root, use

```sh
cd lean
lake build
lake env leanchecker --fresh --verbose SolvedMath.PatternSeparator
```
