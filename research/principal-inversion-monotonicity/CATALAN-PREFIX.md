# Every linear upper strip for an unbounded family of prefix restrictions

In the notation of Claesson, Linusson, Ulfarsson and Verkama, put $B_0=\{213\}$ and form $B_{i+1}$ by inserting a first entry of every possible rank into each member of $B_i$. Write $a_{n,i}(k)$ for the number of permutations avoiding $1324$ and $B_i$ with $k$ inversions. Their Conjecture 4.5 asks for $a_{n+1,i}(k)\ge a_{n,i}(k)$ for all three parameters. Deleting the first $i$ entries leaves a 213-avoider exactly when the original word avoids $B_i$. Indeed any suffix occurrence can use $i$ earlier entries to realize a forbidden pattern, and removing those earlier entries from an occurrence of $B_i$ recovers 213 in the suffix. [Original conjecture and construction](https://arxiv.org/html/2604.01143v2#S4)

**Theorem.** For every finite $C\ge0$ and every $0<\varepsilon\le1$, there are $\eta>0$ and $N$ such that
```math
 a_{n+1,i}(k)\ \ge\ e^{\eta n}a_{n,i}(k)
 \qquad
 \left(n\ge N,\quad 0\le i\le(1-\varepsilon)n,\quad
 0\le\binom n2-k\le Cn\right).
```
Here $i$ and $k$ can both vary with $n$. In particular the conclusion holds on *every* fixed linear upper strip for each fixed index, and for indices occupying any fixed fraction strictly below one. No numerical cutoff on the strip slope $C$ is required.

## A positional cut

Take value complement, so $D=\operatorname{Av}(4231)$, and let $F=\operatorname{Av}(231)$. Every member of $F$ avoids 4231, since its last three entries would give 231. The complemented word belongs to $D$ and its suffix after position $i$ belongs to $F$ up to standardization. Write $l=n-i$ and $j=\binom n2-k$. The desired target has complementary inversion weight $j+n$.

Split any source into its prefix and suffix. Let $x,y,z$ be the numbers of inversions inside the prefix, inside the suffix, and across the cut. Thus $x+y+z=j$. Given the two standardized words and the set of prefix values, the permutation is determined. List the $i$ prefix values as $v_1<\dots<v_i$ on a one-based alphabet. Then $z=\sum_{t=1}^i(v_t-t)$. These differences form a weakly increasing sequence between $0$ and $l$ and, with zeros omitted, give a partition of $z$. Knowing $i$ recovers the zeros. Thus at most $p(z)$ value assignments give this cross weight.

Let $d_i(x),f_l(y)$ denote the respective coefficients of $D,F$. The source count is at most $(j+1)^2\max_{u\le j}p(u)$ times the maximum of $d_i(x)f_l(y)$ over the feasible triples. This prefactor is $\exp(o(n))$ uniformly for $j\le Cn$. For a short proof of the partition estimate, fix $t>0$. Euler's product gives $p(u)\le e^{tu}\prod_{r\ge1}(1-e^{-tr})^{-1}$, and $t$ can be arbitrarily small.

Choose a maximizing triple with positive product. At length $n+1$ use each such prefix followed by a direct sum with every $F$-suffix of length $l+1$ and weight $n+y+z$. This eliminates the cross inversions exactly and supplies a total of $j+n$. Sum closure of $D$ ensures the full word belongs to $D$, and its suffix has the required restriction. The prefix choices are recovered at the prescribed cut. The ratio is therefore bounded below by
```math
 \exp(-o(n))\,f_{l+1}(n+y+z)/f_l(y).
```

The coefficient entropy $s_F$ from the [exact coefficient theorem](ENTROPY.md) is strictly increasing at every finite density, as proved below. We have $0\le y/l\le C/\varepsilon$ and $(n+y+z)/(l+1)\le(C+1)/\varepsilon$. The latter density exceeds $y/l$ by at least $1-o(1)$ uniformly, since $n\ge l$ and $y/l$ is bounded. On this compact interval the difference $s_F(u+1/2)-s_F(u)$ has a positive minimum. The uniform coefficient limit now gives a gain $\exp(\gamma l)$ for some $\gamma>0$, which absorbs the partition factor because $l\ge\varepsilon n$. Empty source coefficients satisfy the assertion automatically. ∎

The cut argument also works for any sum-closed ambient class $D$ with a suffix class $F\subseteq D$ having the same strict finite-density entropy property and the exact coefficient limit. It requires closure only for the direct sums used in the target.

## Why Catalan entropy is strictly increasing

The class $F$ is sum-closed, contains all decreasing blocks, and has growth $4$. For every finite $C$, its permutations with at most $Cn$ inversions have exponential growth strictly below $4$. A proof using bounded independent random-walk blocks follows. The correspondence of inversion weight with Dyck area is classical. [Stump's area-preserving bijections](https://intlpress.com/site/pub/files/_fulltext/journals/joc/2013/0004/0004-a003.pdf)

Write a nonempty 231-avoider as $\alpha\,n\,\beta$. Every value in $\alpha$ is less than every value in $\beta$. Apply the same decomposition to each part after standardizing. The recursion $U P_\beta D P_\alpha$ is bijective with Dyck excursions of $2n$ unit steps. If $A=\sum_{r=0}^{2n-1}H_r$ sums the starting heights of the steps, then $A=n+2\operatorname{inv}(\pi)$. Indeed the maximum contributes $|\beta|$ inversions and the enclosing up and down steps add $2|\beta|+1$ units of height area.

In an unrestricted fair sign word, split the steps into disjoint blocks of $2m$, ignoring a final incomplete block. Within one full block put
```math
 X=\sum_{r=0}^{m-1}|H_{r+m}-H_r|.
```
It depends only on the increments within that block. If the path is nonnegative, the $2m$ heights in those pairs sum to at least $X$. The variables on full blocks are independent and identically distributed, with $\mathbb E X=m\mathbb E|S_m|$ for a length-$m$ simple walk. The latter expectation is at least $\sqrt{m/3}$ by interpolation between the second moment $m$ and the fourth moment $3m^2-2m$.

Choose a fixed $m$ such that $\mathbb E X>(1+2C)m$. Some $t>0$ has $t(1+2C)m+\log\mathbb E e^{-tX}<0$, by the derivative at zero. With $h=\lfloor n/m\rfloor$ full blocks, the probability that their sum is at most $(1+2C)n$ is bounded by $e^{t(1+2C)n}(\mathbb E e^{-tX})^h$, exponentially small in $n$. All Dyck paths with at most $Cn$ inversions belong to that event. There are $4^n$ unrestricted sign words. Hence there is a strict exponential gap for every finite $C$.

The finite-length supremum $s_F(C)$ also lies strictly below $\log4$. A fixed admissible coefficient can be concatenated arbitrarily often at the same density, so it obeys the limiting growth bound on the strip. The [entropy theorem](ENTROPY.md) now gives strict increase throughout the finite density axis.

For $i=n$ the suffix is empty and the class is the full 1324-avoiding class. The argument uses a positive fraction of the positions in the restricted suffix and gives no conclusion at that endpoint.

## Exact entropy at the endpoint

For $i/n\to\alpha\in(0,1)$ and $j/n\to u$ finite, the source's limiting normalized logarithm is
```math
 \max_{0\le v\le u}
 \left[\alpha s_D(v/\alpha)+(1-\alpha)s_F((u-v)/(1-\alpha))\right].
```
For the upper bound, pass to a subsequence along which the maximizing triple's weights divided by $n$ converge. The partition and triple counts cost $o(n)$ in the logarithm. Use monotonicity of $s_F$ to give the cross weight to the suffix. For the lower bound, assign the two factors a total of exactly $j$ inversions with their proportions approaching any chosen $v,u-v$. The direct sum realizes their product, and the coefficient limits apply, including at density zero.

At $\alpha=1$ the entropy is exactly $s_D(u)$. The suffix of length $l=o(n)$ and weight at most $O(n)$ has at most $\binom{l+O(n)}l=\exp(o(n))$ inversion-digit choices. The prefix upper bound follows by continuity of $s_D$; a direct sum with an increasing suffix attains the lower bound. At $\alpha=0$ the roles reverse, and the entropy is $s_F(u)$. Consequently a uniform positive exponential rate reaching $i=n-o(n)$ would require exactly the finite-density entropy gap of the principal class. The fixed-positive-suffix-fraction theorem alone gives a growing ratio on suitably slow diagonals $l/n\to0$, where the exponent per point may tend to zero.

For the unrestricted principal class, every source word with its maximum at or before $(1-\varepsilon)n$ has a 231-avoiding suffix of length at least $\varepsilon n$. A 231 there would extend to 4231 with that maximum. Thus even in the principal comparison, these source objects can be absorbed at an exponential margin. This leaves source objects with the maximum near the right end. Reversing both positions and values gives the corresponding statement about the minimum near the left end.
