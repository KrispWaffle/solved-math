# The rank of the peak in a typical principal downset

Let $M_n$ be the smallest rank that contains the maximum number of distinct patterns of a uniform host. With probability tending to one, that rank is the unique maximum. Define independent $P_s\sim\mathrm{Poisson}(2(s-1))$, $s\ge3$, and put
```math
L=\sum_{s\ge3}\frac{2(s-2)}{2^s-1}P_s.
```
For even $n$, $M_n-n/2$ converges in law to $\lfloor L/4+1/2\rfloor$. For odd $n$, $M_n-\lfloor n/2\rfloor$ converges in law to $\lceil L/4\rceil$. In particular the location of the peak differs from the middle by a tight, integer-valued random displacement. [Rank-unimodality theorem for a uniform host](TYPICAL-HOSTS.md)

## First differences near the middle

Use the separated plot, determining set $B$ of size $b=O((\log n)^8)$, bounded statistic $h$, and conditional averages $g_m$ from the rank theorem. For independent red colors of density $p$ on $B$, the expectation of $h$ is the known finite product $G_{n,D}(p)$ with $D=O((\log n)^2)$. The derivative of this expectation is the sum over $x\in B$ of the expected difference from setting its color red instead of white, with the remaining colors independent of density $p$. This follows by differentiating the finite multilinear expectation in each coordinate before setting all densities equal. [Product for disjoint plot neighborhoods](../../results/distinct-random-permutation-patterns/LENGTH-PROFILE.md)

In the flag construction, condition on the new label $x$ at step $m+1$. The previous $m$ labels are uniform without replacement from the $n-1$ other labels. Thus $n(g_{m+1}-g_m)$ is also a sum of one term per $x\in B$, with this fixed-size law on the remaining colors. On $b-1$ coordinates its distance in total variation from independent colors of density $m/n$ is $O(b^2/n)$ for $m$ near $n/2$. Couple sampling labels with and without replacement from the $n-1$ population, then couple Bernoulli parameters $m/(n-1)$ and $m/n$. The difference of the bounded influences per coordinate is $O(b^2/n)$. Therefore
```math
n(f_{m+1}-f_m)=G_{n,D}'(m/n)+o(1)
```
uniformly on this central interval, on the plot events of probability tending to one. The error is $O(b^3/n+n^{-3})$. The undifferentiated approximation $f_m=G_{n,D}(m/n)+o(1)$ follows by the same color coupling. Here $f_m=D_m/\binom nm$.

For fixed displacement cutoff, the count vector has the previously proved joint Poisson limit. For $q_s(p)=p(1-p)^{s-1}$, the absolute logarithms of $1-q_s$ and their first derivatives are bounded on $[1/3,2/3]$ by a summable multiple of $s(2/3)^{s-2}$ per displacement type. The expected count per type is at most two, and there are $s-1$ types with $d+e=s$. Markov's inequality controls the tails above any fixed cutoff in probability, uniformly in $n$ and $p$. This gives joint convergence of the approximating product and its logarithmic derivative at any finite set of positions $m=n/2+O(1)$. The limiting values at all these positions are respectively $Y_{1/2}>0$ and
```math
\frac{Y'_{1/2}}{Y_{1/2}}=\sum_{s\ge3}\frac{2(s-2)}{2^s-1}P_s=L.
```
The sum is almost surely finite by its expectation and positive by independence. It has no atoms: after conditioning on every group except $s$, any point mass is at most the largest mass of $\mathrm{Poisson}(2(s-1))$, which tends to zero. [Displacement process](../../results/distinct-random-permutation-patterns/LIMIT-LAW.md)

## Determining the mode

At $m=n/2+x$ for fixed admissible $x$, the adjacent binomial coefficient ratio is $(n-m)/(m+1)$. Since the normalizing $f_m$ has a strictly positive limit, the preceding joint limits give
```math
n\left(\frac{D_{m+1}}{D_m}-1\right)\ \Longrightarrow\ L-4x-2 .
```
Any finite collection of these slope tests uses the same $L$. With probability tending to one the ranks are unimodal and these ratios strictly decrease throughout the central and upper range. Positive and negative tests locate all modes between them: below the middle the deterministic first-half increase and, already before the selected positive test, strict log-concavity ensure every earlier value is strictly below the maximum. More explicitly, one can use the deterministic nondecrease through $\lfloor n/2\rfloor$ together with strict ratio decrease starting at $\lceil n/3\rceil$. Tests a fixed distance $K$ on either side of the middle capture the modes with limiting probability tending to one as $K\to\infty$. No specified central ratio equals one with positive limiting probability because $L$ has no atoms. Consequently ties have probability tending to zero. The first integer rank at which the limiting ratio falls below one gives the stated even and odd laws.

Every open subinterval of $[0,\infty)$ has positive probability under $L$. Given an interval of positive width, choose $s$ sufficiently large that its coefficient is smaller than the width and choose an integer value of $P_s$ putting this single term strictly inside. Set the other groups through a large cutoff to zero. This event has positive probability, and the independent tail stays below the remaining margin with positive probability by its vanishing expectation. Thus every even-size offset $0,1,2,\ldots$ and every odd-size offset $1,2,\ldots$ has positive limiting probability in its respective law.
