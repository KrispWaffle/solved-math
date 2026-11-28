# The exact exponential rate of the comparison

Let $D$ be a permutation class closed under direct sum and containing each decreasing permutation. Let $b_n(j)$ count its length-$n$ members with $j$ inversions. Assume $D$ has finite growth rate $\lambda$. Its existence follows from supermultiplicativity. Logarithms are natural. For finite $x\ge0$, define
```math
s(x)=\sup_{m\ge1,\ 0\le j\le xm,\ b_m(j)>0}\frac{\log b_m(j)}m .
```

**Theorem.** For every finite $C\ge0$,
```math
\lim_{n\to\infty}\ \min_{0\le j\le Cn}
\frac{1}{n}\log\frac{b_{n+1}(n+j)}{b_n(j)}
= s(C+1)-s(C).
```
The minimum is over integers, and all these coefficients are positive for sufficiently large $n$. The rate is positive exactly when $s(C)<\log\lambda$.

**Shape of the entropy.** Direct sum maps a pair of fixed lengths injectively to their total length and adds their inversion counts. Thus $s$ is nondecreasing and concave. For the concavity assertion at $(1-t)x+ty$ with $x<y$, choose a single fixed coefficient near each supremum. Repeatedly concatenate blocks of these two types, with the fraction of positions assigned to the second type tending to $t$ from below. The average inversion budget stays within $(1-t)x+ty$, while the normalized log count tends to the corresponding weighted average. Let the two approximation errors tend to zero. Consequently $s$ is continuous on $(0,\infty)$. At zero, $s(0)=0$ and the Lehmer bound $s(x)\le\log G(x)$ proves right continuity. Also $\sup_{x\ge0}s(x)=\log\lambda$. Indeed there are at most $1+\binom m2$ inversion counts at length $m$, so the largest coefficient has the same limiting exponential rate as the total.

**Exact coefficients.** Suppose integers $j_n\ge0$ satisfy $j_n/n\to x$ for finite $x$. A sum of decreasing blocks realizes every such weight at length $n$ for all large $n$. The definition and continuity of $s$ give
```math
\limsup_{n\to\infty} n^{-1}\log b_n(j_n)\le s(x).
```
For $x>0$ take $0<x'<x$ close enough that $s(x')>s(x)-\varepsilon$. Choose a fixed length $m$ and weight $j\le x'm$ with entropy greater than $s(x')-\varepsilon$. Reserve $R_n=\lceil 3\sqrt{2j_n}\rceil+4$ positions and concatenate $\lfloor(n-R_n)/m\rfloor$ blocks from this coefficient. For all large $n$ the inversion total is at most $x'n<j_n$. Fill the remaining inversions with decreasing blocks and pad with singleton blocks to reach length $n$. The prescribed block boundaries recover the choices. As $R_n/n\to0$, the lower limit is at least $s(x)-2\varepsilon$. At $x=0$ the lower bound follows from positivity. The same argument applies along every increasing subsequence of lengths.

By compactness and continuity this convergence is uniform for $0\le j/n\le C$ after subtracting $s(j/n)$. At target length $n+1$ the density is $(n+j)/(n+1)$, uniformly within $(C+1)/(n+1)$ of $1+j/n$. It follows that the normalized log ratio converges uniformly to $s(1+j/n)-s(j/n)$. This increment is nonincreasing by concavity. Its minimum tends to $s(C+1)-s(C)$, as claimed. If the increment vanishes, monotonicity makes $s$ constant on $[C,C+1]$, and concavity makes it constant thereafter. Its eventual value is then $\log\lambda$. The converse follows from the upper bound on $s$. ∎

## Checking a strip with finite block data

For $0<q<1$ let $Z_m(q)=\sum_j b_m(j)q^j$ and $U_m(q)=[m]_q!=\prod_{i=1}^m(1-q^i)/(1-q)$. Write $(q;q)_m=\prod_{i=1}^m(1-q^i)$. Supermultiplicativity gives $\Lambda(q)=\lim_n Z_n(q)^{1/n}=\sup_m Z_m(q)^{1/m}$. For every positive block size $m$,
```math
 Z_m(q)^{1/m}\ \le\ \Lambda(q)\ \le\
 \left(\frac{Z_m(q)}{(q;q)_m}\right)^{1/m}.
```
To prove the upper bound, split an unrestricted length-$n$ permutation into consecutive segments of size $m$, followed by a possibly shorter segment. Conditional on the sets of values in the segments, the inversions across segments are determined. The internal orders therefore have independent weights proportional to $q^{\mathrm{inv}}$. Membership in $D$ requires every complete segment to belong to $D$ after standardization. Hence $Z_n(q)/U_n(q)\le (Z_m(q)/U_m(q))^{\lfloor n/m\rfloor}$. Take $n$th roots and use $U_n(q)^{1/n}\to(1-q)^{-1}$. For fixed $q$, the positive product $(q;q)_\infty$ also shows that the finite upper and lower bounds converge to each other.

In particular $s(C)\le\log\Lambda(q)-C\log q$. When the right side is strictly below $\log\lambda$, the theorem applies. For $D=\operatorname{Av}(4231)$ the length-four block removes exactly the forbidden permutation of weight $q^5$. Let $C_0$ be the positive solution to $G(C_0)=\lambda$. With $q=C_0/(1+C_0)$, the upper bound for the exponential rate gains the strict factor $(1-q^5/U_4(q))^{1/4}$ over $G(C_0)$. Holding $q$ fixed gives a strict inequality on an open interval containing $C_0$. This proves more than the unrestricted Lehmer estimate at its threshold without needing the value of $\lambda$.

The same upper-edge argument applies to a principal forbidden pattern beginning at its minimum and ending at its maximum when the pattern also has a descent. Its complement begins at its maximum, ends at its minimum, and has an ascent. Therefore its avoidance class is sum-closed and contains all decreasing blocks. Excluding the pattern at its own length again gives a strict finite-block improvement.

## The remaining class-specific question

The assertion $s(C)<\log\lambda$ for every finite $C$ would give exponential monotonicity throughout every fixed linear upper strip for 1324. The general hypotheses alone allow equality. For example, a uniformly random layered length-$n$ permutation has independent fair cuts in the $n-1$ gaps. Two positions at distance $d$ form an inversion exactly when the $d$ intervening gaps are uncut. Its expected inversion count is $\sum_{d=1}^{n-1}(n-d)2^{-d}<n$. For every fixed $C>1$, Markov's inequality puts a positive fraction of the $2^{n-1}$ layered permutations in the strip $j\le Cn$. One of the $O(n)$ coefficients has rate $\log 2$, so $s(C)=\log 2$ there. The full principal conjecture also asks for finite lengths and for inversion counts outside these upper strips.
