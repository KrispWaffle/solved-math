# Solved Math

Mathematical conjectures with written proofs and reproducible checks. New results include a Lean theorem stated in the terms of the original problem.

| Result | Conclusion | Verification |
|---|---|---|
| [Separators in permutation-pattern posets](results/pattern-poset-separator/README.md) | The final position of the first window separates the poset for the family proposed by Blitvić, Kammoun, and Steingrímsson. A shared-gap condition extends the theorem to arbitrary overlap sizes. | Lean 4, kernel replay, direct enumeration |
| [Schur positivity of big descents](results/big-descents/README.md) | A tableau formula at each exact longest increasing subsequence length. Cinna Davis recorded the positivity theorem on November 26, 2026. | Written derivation and exact Python checks |
| [No universal packing cutoff](results/packing-cutoff/README.md) | A family of pairs whose packing counts first differ arbitrarily late. Cinna Davis recorded the negative answer on November 26, 2026. | Written derivation and exact Python checks |

The [contents](CONTENTS.md) link to each proof, its scope, and the code. The [history](HISTORY.md) records the earlier proofs and the correction to the first two entries.

## Verify locally

Install Python 3 and the Lean toolchain manager Elan. To run the full suite from the repository root, use

```sh
./scripts/verify.sh
```

The script builds the pinned Lean project, replays the kernel, checks the catalog links, and runs each exact verifier. [Lean declarations and axioms](docs/lean-status.md)

Enable automatic local verification once per clone with

```sh
git config --local core.hooksPath .githooks
```

On push, the hook verifies a clean snapshot of each commit being sent as a branch or tag tip, including pull-request branches. A failed verification stops the push. To verify an incoming pull request, check out its head locally and run the same script.
