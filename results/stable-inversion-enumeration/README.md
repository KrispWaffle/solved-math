# Stable inversion counts for 1243

How many permutations have exactly $k$ inversions and avoid 1243, once their length is large enough? Claesson, Linusson, Ulfarsson and Verkama posed this as Problem 8.3. An occurrence of 1243 consists of four entries in position order whose values satisfy $a<b<d<c$. The authors listed the first ten stable counts. [Problem 8.3 in v2](https://arxiv.org/html/2604.01143v2#S8) · [Problem 8.2 in v1, p. 42](https://arxiv.org/pdf/2604.01143v1#page=42)

For every $k$, the answer counts an ordinary integer partition and a pair of equally long, strictly increasing lists of marks. Write the pairs as $(c_i,u_i)$, with $0\le u_i<c_i$. Charge the size of the partition, every $u_i$, and the first $c_i$ in each consecutive run of marked levels. Count all choices of total charge $k$. For example, the marked levels $2,3,6$ with weights $0,1,4$ contribute $2+6+0+1+4=13$ before adding the ordinary partition. [Generating function and bijection](PROOF.md)

The formula gives the exact count of actual permutations at every length $n\ge k+2$. For each $k\ge1$, the count is strictly smaller one length earlier. The first thirteen terms, beginning at $k=0$, are

```text
1, 2, 5, 10, 20, 37, 66, 114, 193, 317, 511, 810, 1265
```

Lean proves the coefficient identity for every $k$ and every length in this range. The written proof also gives the least length for each individual triple, the full bivariate enumerator, and the sharpness of the threshold. Nakamura's earlier fixed-length algorithm already computes each coefficient when combined with the known stabilization bound. The contribution here is the direct, length-independent formula and its weight-preserving bijection. [Lean source theorem](../../lean/SolvedMath/StableInversionPartitions.lean) · [Independent review and priority search](AUDIT.md) · [Nakamura, §4.1](https://arxiv.org/abs/1301.5080)

Run `python3 results/stable-inversion-enumeration/verify.py` from the repository root for the coefficient checks. Run `./scripts/verify.sh` for the full local build, axiom audit and kernel replay. [Coefficient checker](verify.py) · [Project verification](../../docs/lean-status.md)
