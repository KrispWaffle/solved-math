# History

## November 27, 2026

- Answered Dal Zovo’s recurrence question for generalized shifted tableaux. The formal proof counts the source words, establishes one recurrence per width and excess, and distinguishes the literal-coordinate obstruction from the intended convention. Independently reviewed written proofs give the growth by excess regime. [Problem](results/periodic-set-valued-tableaux/README.md) · [Audit](results/periodic-set-valued-tableaux/AUDIT.md)

- Added a reviewed written proof of Lee and Sah’s random-height conjecture for every cluster poset in Definition 1.3, with an exponential bound for simultaneous deviations. The completed Lean proof derives the conjecture and an all-size exponential bound from finite counts of the original extensions. [Proof](results/lee-sah-cluster-height/PROOF.md) · [Lean scope and review](results/lee-sah-cluster-height/AUDIT.md)

- Added the general algorithmic characterization to the existing separator problem. It classifies every occurrence count using boundary ranks and proves uniform stabilization at $4K+1$. [Proof](results/pattern-poset-separator/CLASSIFICATION.md) · [Review and local checks](results/pattern-poset-separator/CLASSIFICATION-AUDIT.md)

- Moved the [big-descent](archive/big-descents/README.md) and [packing-cutoff](archive/packing-cutoff/README.md) manuscripts and checkers into the archive of later derivations. The separator theorem remains in the original-results catalog.
- Added a Lean proof of the separator assertion in Part I, §7, item 5, and a sufficient condition for any overlap size. [Result and audit](results/pattern-poset-separator/README.md)
- Corrected the novelty assessment of the first two manuscripts. On November 26, Cinna Davis had already posted proofs of the universal packing-cutoff answer at 16:50 UTC and of big-descent Schur positivity at 17:28 UTC. Our manuscripts were first committed on November 27 at 00:27 UTC. Both are retained as later derivations. [Packing-cutoff commit](https://github.com/1337isnot1337/solved-conjectures/commit/2e54a945aa14bb6965f88f9fc21c63e1d9183921) · [Big-descent commit](https://github.com/1337isnot1337/solved-conjectures/commit/16ac09a1dd4f9fa30b1e115c163baf4bc04083a7) · [First local manuscripts](https://github.com/KrispWaffle/solved-math/commit/ff5f6a4ccb63e0193862d0b100d33209411ac1cb)
- Renamed the repository from `permutation-conjectures` to `solved-math`. Each result has its own directory and the Lean proofs share one pinned toolchain.
