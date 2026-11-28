# Which pairs stabilize at the secondary level?

Let $F_d(n)=a(n+1,n+d)-a(n,n+d)$ for the class avoiding 1324 and a second pattern $p$. Write $s_d$ for its eventual slope, whose existence follows for every finite additional basis from the [affinity theorem](PROOF.md).

**Theorem.** Up to inverse and reverse-complement, the six partners $1243,1342,1432,2341,3421,4321$ have a secondary limit sequence. Each of $2143,2413,2431,3412,4231$ has a tertiary limit sequence and fails to have a secondary limit sequence. For $1234$ the diagonal counts eventually vanish. These cases exhaust the distinct partners of length four and prove the classification proposed by Claesson, Linusson, Ulfarsson and Verkama. The secondary sequence for the partner 1342 was previously determined explicitly. [Original table, §5.2](https://arxiv.org/html/2604.01143v2#S5.SS2) · [Problem 8.4 and prior case](https://arxiv.org/html/2604.01143v2#S8)

## Four pairs of templates

Only descriptions with two unbounded increasing intervals contribute a nonzero slope. For each fixed choice of bounded data, the two interval lengths satisfy $x+y=n-c$ with fixed lower bounds, so their contribution has slope one. Descriptions with fewer free intervals contribute slope zero.

Let $U=\gamma\oplus\mathrm{id}_x$ and $V=\mathrm{id}_y\oplus\delta$. The core $\gamma$ is either empty or a nontrivial indecomposable 132-avoider, and $\delta$ is either empty or a nontrivial indecomposable 213-avoider. Empty cores each have weight zero. Write $w=\operatorname{inv}(\gamma)+\operatorname{inv}(\delta)$. The lengths $x,y$ in this section may be taken arbitrarily large at fixed $w$ and fixed additional data. Any fixed lower bounds on them give the same slope. Put $1$ for the singleton permutation.

For decomposable words, the two possibilities for the large left component are $1\ominus U$ and $U\ominus1$. The two possibilities for the right are $V\ominus1$ and $1\ominus V$. The excesses of the end components sum to $w$. Let $D$ be the direct sum of a left and a right component. Inserting a bounded increasing middle block does not change its four-patterns. If an occurrence uses a point of the middle, then at least one side contributes at most one point. Replace that point, if used, and all the chosen middle points by an increasing subsequence of the same length in that side, keeping the other side’s points. Deletion gives the converse.

Let $D_j$ be the number of these decorated choices avoiding $p$ at weight $j$, with $D_j=0$ for negative $j$. In the cancellation from the affinity proof, the new lengths have middle size $0\le m\le h$ and excess sum $d+m+1$. The old lengths have $0\le m<h$ and excess sum $d+m+2$. Their slope difference telescopes to $D_{d+1}$.

For indecomposable words, first normalize a successful boundary deletion to deletion of the first point. Both the middle and the increasing interval in the old last component must now be unbounded to contribute a slope. The old first component followed by the middle is $U$, with a singleton first component absorbed into $x$ when $\gamma$ is empty. Using $v$ from the affinity proof, put $t=v-1\ge0$. The following two forms occur.

- **First and last positions.** The old last component is $(\mathrm{id}\oplus\delta)\ominus1$. The new template $J_t$ has blocks in position order $X,U,M,V,Y$, where $M$ is increasing of length $t$. Their value order is $U<Y<M<X<V$. When $t=0$, the same prescription gives $U<Y<X<V$. The paired decomposable template is $D=(1\ominus U)\oplus(V\ominus1)$.
- **First position and maximum.** The old last component is $1\ominus(\mathrm{id}\oplus\delta)$. Now $J_t$ has position order $X,U,Z,M,V$, with $M$ increasing of length $t+1$ and value order $U<M<X<V<Z$. Its paired template is $D=(1\ominus U)\oplus(1\ominus V)$.

In both forms the excess of $J_t$ is $w+t$. These are exactly the first-rank constructions of the affinity proof. The first form places its restored first value above $t$ entries of the increasing interval and the terminal singleton, the second above $t+1$ entries of the increasing interval. All these words avoid 1324. In the first form, inversions involving $X$ start at the first position and those ending at $Y$ end at the last. In the second form, any inversion involving $X$ starts at the first position and any inversion starting at $Z$ starts at the maximum. Such inversions cannot serve as the middle pair of 1324. The other inversions are inside $U$ or $V$. The block $U$ avoids 132 and has no smaller preceding entry outside it; $V$ avoids 213 and has no larger later entry outside it.

The displayed boundary pair is exactly the set of successful boundary deletions when $x,y$ are large. In the first form, deleting $X$ or $Y$ exposes a direct-sum cut. Deleting the minimum or maximum leaves $X>Y$ spanning every cut. In the second form, deleting $X$ exposes a cut after $U$, and deleting $Z$ exposes a cut before $V$. After deleting the minimum or the last position, the inversion from $X$ to the first point of $M$ and an inversion from $Z$ to the last remaining entry of $V$ still cross every cut. Thus the four disjoint orientations are the displayed two, the inverse of the first, and the reverse-complement of the second. They exhaust all two-variable families by the boundary decomposition. Within an orientation, deleting its designated pivot recovers the old end components, both variable lengths, the cores, and the inserted rank. Counting the two possible successful boundary deletions as separate families would double count.

## A formula for every tertiary limit

For each of the four orientations, let $[p\not\le W]$ be one if the sufficiently long template $W$ avoids $p$ and zero otherwise. Only the two displayed orientations need to be constructed: to test their transformed versions, transform the partner by the same involution. Let $J_e$ count all avoiding indecomposable decorated choices of excess $e$ with two unbounded intervals. Their contribution to $s_d$ is $J_d-J_{d+1}$. Combining this with $D_{d+1}$ gives the identity

```math
\sum_{d\ge-1}s_d q^{d+1}
=\sum_{\text{orientations},\,\gamma,\delta} q^w
\left([p\not\le D]-(1-q)\sum_{t\ge0}q^t[p\not\le J_t]\right).
```

For $d<-1$ the slope is zero. The right hand side is coefficientwise finite because a nontrivial core with $j$ inversions has length at most $j+1$. The identity also gives the tertiary constants at every diagonal, including the signs for classes where counts decrease.

## Finite occurrence certificates

For a length-four partner, four points in each long straight interval suffice, and $t=0,1,2,3,4$ covers all middle lengths. To compare membership in $D$ and $J_t$ for arbitrary cores, take any witnessing occurrence on the side where it exists. Retain just its entries from $\gamma,\delta$ and standardize. Their total length is at most four. The first retained pattern avoids 132, the second avoids 213. Occurrence on the other side for these small patterns lifts to the original cores. Applying this in both directions reduces universal equality to checking 64 pairs of small patterns. The empty patterns are included. The finite check ranges over all subpatterns of these lengths, so they may be decomposable even though the full nonempty cores are indecomposable. [Exact occurrence and coefficient checker](verify.py)

For each of $1243,1342,1432,2341,3421,4321$, membership agrees for every witness pair, orientation and middle length. Thus each summand vanishes since $(1-q)\sum_{t\ge0}q^t=1$. Every slope is zero, proving secondary stabilization along every diagonal.

For the five other representatives it suffices to evaluate the first three coefficients of the identity. Up to weight two the possible indecomposable cores are the empty word, $21$, $231$, and $312$, of weights zero, one, two, and two. Testing the templates gives the following signed slopes. [Reproducible coefficients](verify.py)

| Partner | $s_{-1}$ | $s_0$ | $s_1$ |
|---|---:|---:|---:|
| 2143 | −2 | 0 | 0 |
| 2413 | 3 | 6 | 15 |
| 2431 | 0 | 1 | 2 |
| 3412 | 0 | 2 | 4 |
| 4231 | 0 | 0 | 2 |

Each row has a nonzero slope and therefore a diagonal on which the first difference fails to stabilize. The affinity theorem supplies the tertiary limit on all diagonals. Finally, a permutation avoiding 1234 can be partitioned into at most three decreasing subsequences by grouping entries by the length of a longest increasing subsequence ending there. Its inversion count is at least the sum of their three binomial pair counts, which grows quadratically in $n$. The coefficient at $k=n+d$ is consequently zero for all sufficiently large $n$. This accounts for the trivial partner as well. ∎
