# A uniform limit for the full length profile

For a uniform permutation of size $n$, linearly interpolate the values $D_m/\binom nm$ at $p=m/n$, for every $1\le m\le n$, and assign the interpolant value zero at $p=0$. Write $F_n$ for this continuous function. Then
```math
F_n\ \Longrightarrow\ Y\qquad\text{in } C[0,1]
```
with the supremum norm. The random continuous function $Y$ is the common Poisson product of the length-profile theorem, with $Y_0=0$ and $Y_1=1$. This includes all nonempty lengths and controls deviations uniformly between them. If the empty pattern is counted, its normalized count is the separate deterministic value one. [Product and covariance](LENGTH-PROFILE.md) · [Boundary values](EDGE-LENGTHS.md)

## One flag of red sets

Choose the subsets $S_m$, for all $m$, as the first $m$ labels of a single uniform ordering independent of the plot. Each marginal is a uniform $m$-subset. Write $K_m$ for its occurrence class size. Given the plot, averaging $1/K_m$ over the flag gives exactly $D_m/\binom nm$.

Fix $0<a<1$ and put $t=\lfloor an\rfloor$. Condition on the flag in the independent two-order model. Consider a path system which could occur as the moving part of a preserving bijection at *any* $m\ge t$. If it has $l$ edges and $b$ paths, the common fixed set $A$ consisting of $S_t$ minus its moving vertices has size at least $t-l-b$. Any such bijection fixes $A$. Use only these fixed labels for the insertion bound and allow arbitrary choices among all $n$ labels for the moved labels and the endpoints. There are at most $n^l\binom{n}{b}\binom{l-1}{b-1}$ choices by the enumeration in the mean proof. In the range $l\le8n/\log n$, $|A|\ge an/2$ for sufficiently large $n$. The two orders remain independent given the flag. The insertion and disjoint-edge estimates therefore give the same $C_a^l n^{b-l}l^{2l-b-2\max(b,\lceil l/2\rceil)}$ bound for witnesses over *all* these lengths together. The support between a fixed $M$ and the cutoff has a vanishing tail as $M\to\infty$. Bounded support with $b<l$ costs $o(1)$. Above the cutoff, a union over the at most $n+1$ individual lengths multiplies the previous exponentially small bound by $n+1$. [Path enumeration and bounds](PROOF.md)

For bounded $l=b$, if two edges of a preserving map at any length share a gap of its fixed labels in one order, they also share a gap of $A$ there. The same $O(n^{-b-1})$ insertion estimate in that order and $O(n^{-b})$ in the other order applies to $A$. After summing the choices, the probability is $O(1/n)$. Outside these exceptional events, at every $m\ge t$ each preserving map consists of individually allowable single replacements. For an allowable pair at even one of these lengths, all intervening labels in either coordinate must avoid $S_t$. Given the plot there are at least $\max(d,e)-1$ such labels for a pair of displacements $d,e$, so the expected number of possible pairs with $\max(d,e)>D$ is at most
```math
2\sum_{\max(d,e)>D}(1-t/n)^{\max(d,e)-1}.
```
This tends to zero as $D\to\infty$, uniformly for all sufficiently large $n$. Here the flag is averaged given the plot, while the preceding path argument conditioned on the flag.

For fixed $D$, with probability tending to one the short pairs have disjoint determining neighborhoods in the plot. On this event every subset of the individually allowable short pairs can be switched, simultaneously at each length, and each choice produces a different image. Together with the previous two paragraphs, this bounds the probability that $1/K_m$ differs from $2^{-W_{m,D}}$ for **at least one** $m\ge t$ by a quantity tending to zero as first $n$ and then $D$ tend to infinity. Here $W_{m,D}$ counts the allowable short pairs. [Separation of the strips](LIMIT-LAW.md)

The maximum of the differences of the conditional expectations is bounded by the conditional expectation of the maximum of the differences. On a separated plot with at most $H$ short pairs the exact colors on at most $2DH$ labels differ in total variation from independent colors of density $m/n$ by at most $\binom{2DH}{2}/n$, uniformly in $m$, by coupling sampling with and without replacement until the first repeated draw. The number of pairs is tight for fixed $D$. With the finite product $G_{n,D}$ of the length-profile proof, these observations give
```math
\lim_{D\to\infty}\limsup_{n\to\infty}
\mathbb E\max_{t\le m\le n}
\left|\frac{D_m}{\binom nm}-G_{n,D}(m/n)\right|=0 .
```
Interpolation costs at most $C_D n^{-1}\sum_{d,e\le D}N^{(n)}_{d,e}$ for fixed $D$, by the derivative bound there. The fixed products converge as continuous functions, and their limits converge almost surely uniformly on $[a,1]$ by summable domination with $1-a$. This proves $F_n\Rightarrow Y$ in the supremum norm on $[a,1]$. [Product approximation](LENGTH-PROFILE.md)

## Controlling all short patterns together

Take an integer $s$ with $2s\le n/2$. Count in $Z_s$ the pairs joining a label in $S_s$ to a label outside $S_{2s}$, with no intervening label of $S_{2s}$ other than the red endpoint in either order. For every $s\le m\le2s$ these pairs remain individually allowable, so $K_m\ge1+Z_s$ simultaneously. Set $M=2s$ and $u=n-M$. The one-order probabilities from the edge proof apply to the $M$ blocking reds, of which $s$ are eligible endpoints. Thus $\mathbb E Z_s=4su/(M+1)^2$. In the second factorial moment the disjoint term is at most $(\mathbb E Z_s)^2$ since $(4M+2)(M+1)\le4M(M+2)$. Relative to $(\mathbb E Z_s)^2$, the shared-red and shared-white terms are $O(1/s+1/u)$ by the same exact formulas. The diagonal costs $1/\mathbb E Z_s=O(s/n)$. Chebyshev's inequality at $\tfrac12\mathbb E Z_s$, followed by conditioning on the plot, now gives
```math
\mathbb E\max_{s\le m\le2s}\frac{D_m}{\binom nm}
\le\mathbb E(1+Z_s)^{-1}=O(1/s+s/n).
```
[Two-pair probabilities](EDGE-LENGTHS.md)

For $1\le m\le n^{1/3}$ the deterministic upper bound $m!/\binom nm\le(m^2/(n-m+1))^m$ tends to zero uniformly. Starting at $s_0=\lfloor n^{1/3}\rfloor$, sum the interval estimates for $s=2^j s_0$ as long as $s\le\lceil an\rceil$, taking $a<1/8$. The sum is $O(n^{-1/3}+a)$. This proves $\lim_{a\downarrow0}\limsup_n\mathbb E\sup_{0\le p\le a}F_n(p)=0$. The limit $Y$ is almost surely continuous at zero with value zero by the square-shell argument in the edge proof. Extend each restriction on $[a,1]$ by a line from zero to its value at $a$. The error in supremum norm is at most twice the supremum on $[0,a]$. Apply the preceding estimates and let $a\downarrow0$ in bounded Lipschitz tests. This proves the claimed convergence on $[0,1]$.
