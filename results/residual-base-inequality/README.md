# Meng’s base inequality for 1324-avoiding permutations

Every base residual $\rho$ has at least $3|\rho|-15$ inversions. Equivalently, its length is at most its defect plus eight. This resolves Conjecture 6.7 for every length and defect. Exactly four base residuals attain equality. Meng listed the four in the original paper. [Source, version 2, §6.5](https://arxiv.org/html/2609.06717v2#S6.SS5)

The proof shows that the inversion count of a reduced 1324-avoiding skeleton grows at least quadratically with its length. From length 44 onward that estimate suffices. For the remaining lengths two independent exhaustive searches give the same census of possible counterexamples. [Proof and equality cases](PROOF.md) · [Independent mathematical review and prior work](AUDIT.md) · [Census by length](census.tsv)

Lean proves the bound at all skeleton lengths at least 44 and the implication from the precise finite census to Meng’s full conjecture. Two C++ programs discharge that finite statement outside Lean. Run the following from the repository root with Python 3 and a C++20 compiler. [Lean source](../../lean/SolvedMath/ResidualBase.lean) · [Verification script](verify.py)

```sh
python3 results/residual-base-inequality/verify.py
```
