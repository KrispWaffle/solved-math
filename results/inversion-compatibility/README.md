# Which restrictions does the Linusson–Verkama injection preserve?

A pattern $p$ is *compatible* if growing any decomposable or almost decomposable permutation avoiding both 1324 and $p$ by the authors’ prescribed injection still avoids $p$. The boundary priority is part of the definition. Claesson, Linusson, Ulfarsson and Verkama proved that almost every 1324-avoiding pattern is compatible and gave two criteria which left individual patterns undecided. [Definition 7.4, Theorems 7.6–7.9 and Table 2](https://arxiv.org/pdf/2604.01143v2#page=28) · [Original injection](https://arxiv.org/abs/2408.15075)

**Every individual pattern admits an exact quadratic-time test.** It reads four orientations of the pattern and their direct-sum components. On failure it constructs a witness of length at most $|p|+2$. This proves that the authors’ finite search window suffices at every length. The pattern $364251$ requires both extra points. [Classification](CLASSIFICATION.md) · [Maximum-leading patterns](FIRST-MAXIMUM.md) · [Sharp witness bound](SHORT-WITNESSES.md) · [Algorithm](decision.py)

**Compatibility of every explicitly given finite set of forbidden patterns is decidable in polynomial time.** If a forbidden $p$ appears in an image, some input avoiding the whole set has length at most $|p|+18$ and already contains $p$ with at most two points deleted. The algorithm can therefore search polynomially many extensions of subpatterns of $p$. The exponent of this general search is large. [Compression and algorithm proof](PROOF.md)

The results determine which restrictions inherit the source injection's monotonicity bound for $k\le2n-7$ directly by compatibility. The paper's separately numbered Problem 8.1 asks for monotonicity at **all** lengths and inversion counts for some four-letter partner. For the partner 1342 that stronger assertion already follows from a published Schröder-polynomial recurrence. [Prior result and derivation](AUDIT.md#the-separate-all-length-question) [Original problem](https://arxiv.org/pdf/2604.01143v2#page=36)

## Verification

The classification and the finite-basis theorem have independently reviewed written proofs. Lean models the physical injection and checks pivot comparisons, an occurrence replacement inside a 213-avoiding block, overlapping windows and the explicit length-eight incompatibility certificate. The general classification and witness bound have partial Lean verification. [Lean source](../../lean/SolvedMath/InversionCompatibility.lean) · [Review and prior-work checks](AUDIT.md)

Run the full suite from the repository root with `./scripts/verify.sh`. To reproduce all seven entries of the source table or obtain a witness, run

```sh
python3 results/inversion-compatibility/verify.py --table
cd results/inversion-compatibility
python3 -c 'from decision import find_witness; print(find_witness([(3,6,4,2,5,1)]))'
```
