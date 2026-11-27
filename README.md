# Solved Math

Mathematical conjectures with written proofs and reproducible checks. Each result states the original problem and identifies the parts verified in Lean.

## Results

| Result | Conclusion | Verification |
|---|---|---|
| [Lee–Sah cluster-poset heights](results/lee-sah-cluster-height/README.md) | All marked ranks in a uniform extension concentrate simultaneously on the inverse beta curve. | Full Lean proof, independent mathematical review, exact rank checks |
| [Separators in permutation-pattern posets](results/pattern-poset-separator/README.md) | For every compatible overlap, boundary ranks decide separator existence at any occurrence count. Existence stabilizes by $4K+1$ windows for pattern length $K$. The proposed overlap-two family also has an explicit separator. | Lean 4, kernel replay, direct enumeration |

The [contents](CONTENTS.md) link to the proofs, their scope, and the code.

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
