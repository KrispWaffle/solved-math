# The base inequality

**Theorem.** Every base residual permutation $\rho$ in Meng’s Conjecture 6.7 satisfies

```math
\operatorname{inv}(\rho)\ge 3|\rho|-15.
```

Equality holds exactly for the four permutations listed in the source. The proof has an unrestricted quadratic estimate and an exhaustive finite calculation. [Meng, version 2, §6.5](https://arxiv.org/html/2609.06717v2#S6.SS5)

## The skeleton

A permutation avoids 1324 when there are no positions $i<j<k<l$ with values $v_i<v_k<v_j<v_l$. A bond is an adjacent pair of positions whose values increase by one. A reduced permutation has no bonds. A sum cut is a nonempty proper prefix containing the smallest values of the permutation.

Take a reduced, sum-indecomposable 1324-avoider $\sigma$ of length $s\ge2$. Among its first and last positions and the positions of its minimum and maximum, let $D$ consist of those whose deletion creates a sum cut. At length two take both positions. Assign each position $i$ a block width $b_i=1+\mathbf{1}_{i\in D}$. Inflating each entry to an increasing block of consecutive ranks of this width gives the base residual $\rho$. Meng’s skeleton theorem covers every base residual in this way. Its length $N$ and inversion count $K$ satisfy

```math
N=s+|D|\le s+4,\qquad
K=\sum_{i<j,\ \sigma_i>\sigma_j} b_i b_j\ge \operatorname{inv}(\sigma).
```

Indeed, the two blocks over an inverted pair contribute all their cross pairs. [Meng, Theorem 5.3 and Proposition 6.3](https://arxiv.org/pdf/2609.06717v2#page=15)

## Peeling the outer positions

For $u\ge0$ put $t=\lfloor u/2\rfloor$ and $T(j)=j(j+1)/2$. Define

```math
B(u)=\sum_{d\ge0}\max(t-2d,0)
    =T(\lfloor t/2\rfloor)+T(\lceil t/2\rceil).
```

**Lemma.** A reduced 1324-avoider of length $s$ has at least $B(s)$ inversions. More generally, consider a contiguous word of $m$ distinct integer values in such a permutation. If its alphabet is the union of $g+1$ maximal consecutive intervals, the word has at least $B(\max(m-g,0))$ inversions.

For the general assertion, repeatedly remove both outer positions and charge all inversions incident to at least one of them. After $d$ steps the word has length $h=m-2d$. Its alphabet has at most $g+2d$ gaps between consecutive intervals, since each deletion can create at most one new gap. Standardize its values to $1,\ldots,h$. Each bond in the standardized word uses a distinct alphabet gap. Otherwise the actual adjacent entries would have been a bond in the original permutation. Thus the standardized word has at most $g+2d$ bonds.

Suppose its endpoints are $a<b$. Every value in $[a,b]$ occurs in increasing order relative to the other values of that interval. A descent in the interior subsequence gives a 1324 occurrence with the two endpoints. Write $q=h-(b-a+1)$ for the number of values outside the interval. Each such value inverts exactly one endpoint, and these account for all endpoint inversions. The increasing chain has $h-q-1$ pairs of successive values. At most $q$ of these pairs can be interrupted by an outside entry, so at least $h-1-2q$ survive as bonds. Consequently the charge satisfies

```math
q\ge \left\lceil\frac{h-1-g-2d}{2}\right\rceil
=\left\lfloor\frac{m-g}{2}\right\rfloor-2d.
```

For decreasing endpoints, each interior entry inverts at least one of the two endpoints, and the endpoints themselves invert. The charge is at least $h-1$, which also satisfies the bound whenever $h\ge2$. The right hand side can be positive only while two positions are available. Inversions charged in different steps are disjoint. Summing proves the lemma. A complete permutation has $g=0$.

For $s\ge44$, the first eleven charges give

```math
\operatorname{inv}(\sigma)\ge 11\lfloor s/2\rfloor-110\ge3s-3.
```

The last inequality holds at 44 and 45, and raising $s$ by two increases its left hand side by eleven and its right hand side by six. Therefore $K\ge3s-3\ge3N-15$ for every $s\ge44$.

## The remaining finite statement

For $2\le s\le43$, a violation would have $\operatorname{inv}(\sigma)\le3s-4$. The following search covers exactly the reduced 1324-avoiders under that cap. It builds a permutation from the outside in, storing a prefix, a suffix, and the unused values in the open interval of positions between them.

1. When filling the left end of the interval, charge one inversion for each unused value smaller than the selected entry. When filling its right end, charge one for each unused value larger than the entry. This counts every inversion once. Discard a branch when the accumulated cost plus the lemma’s bound on the unfilled interval exceeds the cap.
2. Require that the filled positions contain no copy of 1324 and no originally adjacent filled positions make a bond. Each rejection persists in every completion.
3. If the smallest prefix value is $a$ and the largest suffix value is $b>a$, the remaining values strictly between $a$ and $b$ must occur in increasing order, by the same endpoint argument. Only their smallest can be taken next from the left, or their largest from the right. Every pair of these values differing by one must be separated by some remaining value outside this set to prevent a bond. If the number of such pairs exceeds the available separators, discard the branch.
4. At a leaf, discard sum-decomposable permutations. For each of the four extreme positions, test a sum cut after deletion and relabeling. Compute $N$ and $K$ from the block widths above and compare $K-3N+15$ with zero.

These tests reject only impossible completions. Every surviving word has a unique path because the order of the positions filled is fixed. The census found **2,785,878** reduced avoiders within the cap, of which **2,132,228** were indecomposable. The smallest base margin was zero. A separate search growing the permutation from the left agreed at every length. The per-length table records the reduced and indecomposable counts, minimum margin, equality count and violation count. [Outside-in implementation](census.cpp) · [Per-length census](census.tsv) · [Reproduction and literal small-order check](verify.py) · [Independent review](AUDIT.md)

## Equality

If $\operatorname{inv}(\sigma)\ge3s-3$, equality would force $N=s+4$ and $K=\operatorname{inv}(\sigma)$. The first equality requires four doubled positions. Every position in a sum-indecomposable permutation of length at least two is incident to an inversion. Indeed, an isolated position has all smaller values before it and all larger values after it, giving a proper sum cut on at least one side. Doubling any position therefore strictly increases the inversion count. This excludes equality outside the finite census, including all lengths $s\ge44$.

Within the census equality occurs for two skeletons of length 9 and two of length 13. Their base residuals in one-based notation are

| Base length | Permutation | Inverse |
|---|---|---|
| 11 | 4 3 5 8 1 2 9 11 10 6 7 | 5 6 2 1 3 10 11 4 7 9 8 |
| 13 | 4 3 5 7 2 8 10 1 11 13 12 9 6 | 8 5 2 1 3 13 4 6 12 7 9 11 10 |

Meng exhibited these four examples. The argument proves that this list is exhaustive at every length and defect. Since $\delta(\rho)=K-2N+7$, the inequality is equivalently $N\le\delta(\rho)+8$.
