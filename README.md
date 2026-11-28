# Solved Math

Mathematical conjectures with written proofs and reproducible checks. Each result states the original problem and identifies the parts verified in Lean.

## Results

| Result | Conclusion | Verification |
|---|---|---|
| [Lee–Sah cluster-poset heights](results/lee-sah-cluster-height/README.md) | All marked ranks in a uniform extension concentrate simultaneously on the inverse beta curve. | Full Lean proof, independent mathematical review, exact rank checks |
| [Vertex connectivity of a random inversion graph](results/random-inversion-connectivity/README.md) | Connectivity equals minimum degree with probability tending to one. The probability of strict inequality is asymptotic to $1/n$. | Reviewed written proofs, partial Lean verification, exhaustive separator checks |
| [Higher inversion limits for 1324](results/higher-inversion-limits/README.md) | The diagonal differences are eventually affine for every finite additional basis. The proof classifies when each pair stabilizes and gives all five tertiary series. | Reviewed written proof, partial Lean verification, exact signed coefficients |
| [Compatible restrictions for the 1324 inversion injection](results/inversion-compatibility/README.md) | A quadratic-time test classifies every singleton and constructs a witness with at most two extra entries. Every finite basis admits polynomial-time recognition. | Reviewed written proofs, partial Lean verification, direct injection checks |
| [Meng’s base inequality](results/residual-base-inequality/README.md) | Every base residual has at least three times its length minus fifteen inversions. Exactly four attain equality. | Reviewed computer-assisted proof, partial Lean verification, two exhaustive searches |
| [Stable inversion counts for 1243](results/stable-inversion-enumeration/README.md) | A marked-partition formula gives every stable coefficient. It counts the actual length-$n$ permutations as soon as $n\ge k+2$ for $k$ inversions. | Full Lean proof, independent mathematical review, exact enumeration |
| [Attainable derangement limits](results/derangement-limit-spectrum/README.md) | Every value in $[0,1]$ occurs at every prescribed growth rate at least Bevan’s constant. Polynomial-growth classes attain exactly the rationals. | Reviewed written proofs, complete Lean witnesses for all rationals, partial Lean for all reals |
| [Distinct patterns in a random permutation](results/distinct-random-permutation-patterns/README.md) | The expected fraction tends to $e^{-2}$. One random curve gives the joint limiting law across all nonempty pattern lengths. | Reviewed written proof, partial Lean verification, exact enumeration |
| [Set-valued tableaux on periodic shifted diagrams](results/periodic-set-valued-tableaux/README.md) | A finite transfer counts every excess. For each fixed excess, one recurrence works for all outlines at a given width. | Lean proof of the recurrence and coordinate obstruction, reviewed written asymptotics |
| [Separators in permutation-pattern posets](results/pattern-poset-separator/README.md) | For every compatible overlap, boundary ranks decide separator existence at any occurrence count. Existence stabilizes by $4K+1$ windows for pattern length $K$. The proposed overlap-two family also has an explicit separator. | Lean 4, kernel replay, direct enumeration |

The [contents](CONTENTS.md) link to the proofs, their scope, and the code.

## Verify locally

Install Python 3, a C++20 compiler available as `c++`, and the Lean toolchain manager Elan. To run the full suite from the repository root, use

```sh
./scripts/verify.sh
```

The script builds the pinned Lean project, replays the kernel, checks the catalog links, and runs each exact verifier. [Lean declarations and axioms](docs/lean-status.md)

Enable automatic local verification once per clone with

```sh
git config --local core.hooksPath .githooks
```

On push, the hook verifies a clean snapshot of each commit being sent as a branch or tag tip, including pull-request branches. A failed verification stops the push. To verify an incoming pull request, check out its head locally and run the same script.
