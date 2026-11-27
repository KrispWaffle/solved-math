# Permutation conjectures

Two proofs about permutation patterns, with exact checks written in standard-library Python.

| Result | What the proof establishes |
|---|---|
| [Big descents and Schur positivity](big-descents/proof.md) | Proves Elizalde–Rivera–Zhuang's Conjecture 4.9. Each Schur coefficient counts pairs of tableaux, even when the longest increasing subsequence length is fixed exactly. |
| [No universal packing cutoff](packing-cutoff/proof.md) | Answers the universal-cutoff question of Blitvić, Kammoun, and Steingrímsson in the negative. For every $k\ge2$, two patterns with the same length and overlap agree through $k$ prescribed occurrences and differ at $k+1$. |

The [research log](research-log.md) records the derivations, prior-work searches, and verification scope. Both manuscripts are research drafts.

## Run the checks

From the repository root, run

~~~sh
python3 big-descents/verify.py
python3 packing-cutoff/verify.py
~~~

The first program enumerates permutations and compares their big-descent sets with the tableau formula. The second counts rank assignments satisfying the original window constraints. Both use exact integer arithmetic.
