# Minimum separators in the random permutation graph

For a uniform permutation of $[n]$, let $G$ be its inversion graph, $d$ its minimum degree and $\kappa$ its vertex connectivity. Then
```math
\Pr(\kappa\ne d)=O((\log n)^3/n).
```
In fact, outside an exceptional event of this probability, every minimum separating set is the neighborhood of a vertex that it isolates. Consequently $\Pr(\kappa/\sqrt n>x)\to e^{-x^2}$ for each $x>0$. The limit for $d$ is Bhattacharya and Mukherjee’s theorem. [Verkama’s question](https://arxiv.org/html/2611.17237v1#S6) · [Minimum-degree theorem 3.7](https://arxiv.org/abs/1503.03582)

## A cut in the permutation diagram

Use one-based coordinates $(p,v)=(p,\pi(p))$. A pair of thresholds $i,j$ gives a southwest rectangle $p\le i,v\le j$ with $A$ points and a northeast rectangle $p>i,v>j$. Their crossing set consists of points satisfying just one of the two weak inequalities. Its size is $c=i+j-2A$. Removing it separates the two rectangles whenever both contain points.

Conversely a minimum separating set is such a crossing set. Among the remaining vertices, the positions of a connected component form an interval in their order: any surviving point between the endpoints of an inversion is adjacent to at least one endpoint, and the intervals of the edges along a path cover the positions between the ends of the path. No inversion crosses between distinct components. Hence the first component has all its values below the remaining components. Take $i,j$ to be its largest position and value. Every crossing vertex was deleted, and both rectangles still contain survivors. Minimality gives equality of the two sets. This is the classical scanline representation of separators in permutation graphs. The complete graph has $\kappa=d=n-1$ directly. [Bodlaender–Kloks–Kratsch, §3](https://pure.tue.nl/ws/files/4297898/390171.pdf)

For a southwest point $(p,v)$ its degree is at most $p+v-2$, since each neighbor is either earlier in position or lower in value. Thus, whenever $c\le d$,

```math
(i-p)+(j-v)\le 2A-2 .
```

If $A\ge2$, this forces two different points at coordinate distances at most $2A-2$ in both directions. The same statement holds at the northeast corner after reversing both coordinates.

## Localizing the thresholds

All estimates below hold for sufficiently large $n$. Put $b=\lceil\sqrt{4n\log n}\rceil$, $D=2b$ and $w=17D$. The first $b$ positions miss the smallest $b$ values with probability at most $(1-b/n)^b\le n^{-4}$. A point in that corner implies $d\le 2b=D$.

For a crossing set of size $c\le D$, the identity for $c$ gives $|i-j|\le D$. Reverse both coordinates if needed so that $i\le n/2$. Then $j\le n/2+D\le3n/5$. Except with probability exponentially small in $D$, more than $D$ of the first $16D$ entries have value greater than $3n/5$. To fail this test at least $15D$ prescribed-or-chosen entries must all have values at most $3n/5$. Sampling without replacement bounds its probability by
```math
\binom{16D}{D}(3/5)^{15D}\le [16e(3/5)^{15}]^D.
```
Require the same event in the reversed coordinates. If $i\ge16D$, these entries all cross the putative cut, contradicting $c\le D$. Consequently $i<16D$, $j\le17D$, and the southwest rectangle lies in the corner square of side $w$ in one of the two orientations.

## Small rectangles rarely contain a close pair

Let $Y$ count permutation points in that square. For each integer $l\ge1$,
```math
\Pr(Y\ge l)\le\binom{w}{l}(w/n)^l\le(ew^2/(nl))^l.
```
Take $l=\lceil10ew^2/n+4\log n\rceil=O(\log n)$. Except with probability at most $n^{-4}$ we have $Y<l$. For a close pair of points in the square, there are at most $2wl$ choices of increasing positions less than or equal to $2l$ apart and at most $4wl$ choices of distinct ordered values less than or equal to $2l$ apart. Two prescribed distinct positions and values have probability $1/(n(n-1))$. Hence the probability of any such pair in either corner is $O(w^2l^2/n^2)=O((\log n)^3/n)$.

On the event just described, any nonempty separating rectangle with $c\le d$ has a singleton on its corner side. Indeed its number of points is less than $l$, and two of them would be a close pair by the deterministic bound. Its vertex has all its neighbors in the crossing set, so $d\le c$. For a noncomplete graph, deleting the neighbors of a minimum-degree vertex separates it from at least one nonneighbor, giving $\kappa\le d$. Apply the rectangle conclusion to a minimum cut. It has size $d$ and is exactly the neighborhood of its isolated vertex. The distributional consequence follows by comparing the two tail probabilities at each threshold.
