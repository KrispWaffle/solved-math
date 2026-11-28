# The probability of an exceptional permutation

With $G$ the inversion graph of a uniform permutation of $[n]$,
```math
\Pr\{\kappa(G)<d(G)\}\sim \frac1n .
```
The dominant exceptions have an adjacent descending pair of consecutive values in a diagonal corner. The proof below concerns strict inequality of the graph parameters. [Definitions and scanline proof](PROOF.md)

## Controlling the corners uniformly

A strict cut is a separating scanline with crossing count $c<d$. Its existence is equivalent to $\kappa<d$. Use the localization of the main proof, with exceptional probability $o(1/n)$, to put a candidate rectangle in the southwest corner in one of the two orientations and ensure $i+j=O(\sqrt{n\log n})$. Write $s\le i+j<2s$ with $s$ a power of two. Let $Y$ count points of the square $[2s]^2$. Write $A$ for the rectangle’s population. Strictness implies $A\ge2$, and two points of the rectangle have both coordinate distances at most $2Y$.

A further necessary event $E_s$ is that $Y\ge s/4$ or the square $[\lfloor s/4\rfloor]^2$ is empty. Indeed, if $Y<s/4$ then $c=i+j-2A>s/2$ and any point of the small square would have degree less than $s/2$. Fix any two distinct positions and two distinct assigned values in $[2s]^2$. Conditional on these two prescribed points, the other $n-2$ positions receive a uniform permutation of the remaining values. All the following estimates are uniform in the two prescriptions and in this range of $s$.

* The probability of $E_s$ is at most $C\exp(-c_1s^2/n)$ for absolute constants. For an empty small square at least $\lfloor s/4\rfloor-2$ relevant rows and as many columns remain, so the empty-square estimate from the main proof applies. For $Y\ge s/4$, there must be at least $t=\lceil s/4\rceil-2$ further hits. For any $t\ge1$ the probability of at least $t$ further hits is at most $(C_1s^2/(nt))^t$, by choosing the rows of the hits. For $s$ sufficiently large and $s=o(n)$ this gives an exponential upper bound in $s$. Bounded $s$ is absorbed in $C$.
* Put $\mu=1+s^2/n$. The same bound gives
```math
\sum_{u,v\ge1}\Pr(2Y\ge\max(u,v)\mid\text{prescriptions})^{1/2}\le C_2\mu^2.
```
Here the conditional law of $Y$ is identical for all the prescriptions. There are fewer than $2h$ pairs with $\max(u,v)=h$. Sum these trivially through a sufficiently large constant times $\mu$. Beyond that, the probability decays geometrically in $h$, by the preceding hit bound.

For fixed positive distances $u,v$ there are $O(s^2)$ placements of the pair in the square, including the two orientations of its values. Each prescription has probability $1/(n(n-1))$. Apply Cauchy–Schwarz to the conditional probability of $E_s$ and $2Y\ge\max(u,v)$. The probability of a strict cut at this scale is at most
```math
C_3\frac{s^2}{n^2}(1+s^2/n)^2\exp(-c_2s^2/n).
```
The sum over all dyadic scales is $O(1/n)$. The sum over scales $s\ge K\sqrt n$ is $o_K(1)/n$, meaning that its constant tends to zero as $K\to\infty$. Thus it suffices to count cuts in the two fixed corner squares of side $K\sqrt n$, allowing a change by an absolute factor in $K$.

## The only leading configuration

For fixed $K$, the population of either such square exceeds $C_K\log n$ with probability $O_K(n^{-3})$, by the same row-choice bound. If $A\ge3$, all the rectangle’s points are within $O_K(\log n)$ of its upper right corner in both coordinates. A triple in the square this close has expected count $O_K((\log n)^4/n^2)$. Indeed there are $O_K(\sqrt n(\log n)^2)$ position triples and the same order of value triples, and the probability for each prescribed matching is $1/(n(n-1)(n-2))$. Such rectangles contribute $o(1/n)$.

If $A=2$, a point $(a,b)$ in the rectangle satisfies $i+j-4=c<d\le a+b-2$. Its deficits therefore satisfy $(i-a)+(j-b)\le1$. The only two distinct positions with distinct values in these three possible cells are $(i-1,j)$ and $(i,j-1)$. Set $p=i-1$, $v=j-1$. This is the bond $\pi(p)=v+1$, $\pi(p+1)=v$. [Kernel-checked geometric statement](../../lean/SolvedMath/RandomInversionConnectivity.lean)

Condition on this bond and delete it. The remaining permutation is uniform on $n-2$ after standardization. Write $d'$ for its minimum degree. In a fixed corner square and for all sufficiently large $n$, the probability that the bond supports a strict cut is bounded below by $\Pr(d'\ge p+v-1)$ and above by $\Pr(d'\ge p+v-3)$.

For the lower bound, a third southwest point would have degree at most $p+v-4$ after standardization, so it is absent. The northeast side is occupied since $n>p+v$. The two bond entries have degree $p+v-1$ and the crossing set has size $p+v-2$. All other degrees are at least $d'$, proving strictness. For the upper bound, when the bond supports this two-point strict cut, all degrees exceed $p+v-2$. Deleting its two vertices decreases the degrees of survivors by at most two.

Bhattacharya and Mukherjee’s minimum-degree limit has continuous tail $e^{-x^2}$. Convergence of distribution functions to a continuous limit is uniform on compact intervals. The conditional probability above therefore differs from $\exp(-(p+v)^2/n)$ by $o_K(1)$ uniformly in the corner box. Each bond has unconditional probability $1/(n(n-1))$. [Bhattacharya–Mukherjee, Theorem 3.7](https://arxiv.org/abs/1503.03582)

Double counting contributes $O_K(n^{-2})$. Two bonds with disjoint positions and values prescribe four points, with $O_K(n^2)$ choices of the two bonds across both boxes. Overlap in only a position or only a value is inconsistent. Two compatible overlapping bonds form a decreasing consecutive triple, with $O_K(n)$ choices of its first position and value. For large $n$ the two corner boxes have disjoint coordinates. Bonferroni’s inequalities justify replacing the union by the sum to first order.

Multiplying by $n$, summing over $p,v$ in the two boxes, and sending $n$ and then $K$ to infinity gives
```math
2\int_0^\infty\int_0^\infty e^{-(x+y)^2}\,dx\,dy
=2\int_0^\infty t e^{-t^2}\,dt=1.
```
The dyadic estimate justifies the passage from the fixed boxes to the whole diagram.
