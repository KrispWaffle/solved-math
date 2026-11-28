# Rank-unimodality for nonperiodic hosts and random finite-alphabet words

**Theorem.** Fix an alphabet bound $M\ge2$, a density $\delta>0$ and constants $C>0$ and $a\ge0$. Consider a host with $k$ parts in $\{1,\ldots,M\}$, of which at least $\delta k$ equal $M$. Suppose every run of parts smaller than $M$, including both end runs, has length at most $C(1+\log k)^a$. Every sufficiently long such host has a unimodal sequence of ranks in generalized subword order. The threshold is uniform over all orders and choices of the parts under these hypotheses. There is also a Gaussian law for the rank of a uniformly chosen distinct subword and a formula locating all the modes to within half a rank plus a vanishing error.

**Random hosts.** For independent identically distributed positive letters with any fixed finite support, almost surely every sufficiently long prefix has a rank-unimodal principal ideal. For a maximum letter of mass $p>0$, the strong law gives density at least $p/2$ eventually. For $0<p<1$, the probability of a run of at least $h$ smaller letters among the first $k$ is at most $k(1-p)^h$. Taking $h=\lceil c\log k\rceil$ with $c>3/|\log(1-p)|$ gives a summable bound. Borel–Cantelli proves the assertion. A constant word of maximum at least two also satisfies the deterministic hypotheses. For the one-letter alphabet consisting of one, every rank has one word. Vatter's general conjecture includes hosts with arbitrary alphabets and gap lengths. [Conjecture 2.6](https://arxiv.org/pdf/2602.16355v4#page=7)

## Splitting at the maximum

Write the host as $W=A_0 M A_1 M\cdots M A_m$, with $m\ge\delta k$ occurrences of $M$. Put $N=|W|$ for its total weight. Let $B_i=F_{A_i}$ count distinct subwords by weight, $S=x+\cdots+x^M$, and $Q_i=1+(S-1)B_i$. The maximal-part identity and induction give two exact expressions

```math
P=\prod_{i=0}^{m}Q_i=1+(S-1)F_W,\qquad
F_W=\sum_{j=0}^{m}B_j P_j,\qquad P_j=\prod_{i<j}Q_i. \tag{1}
```

All coefficients on the right of the sum are nonnegative. Indeed, $Q_i=F_{A_i M}-F_{A_i}$ counts words newly available after appending $M$. Its support is an integer interval containing at least two degrees. Extend a minimum-weight new word by one unit at a time inside $A_iM$ until it reaches the host, keeping the word outside the old ideal. The two highest weights are both present because lowering the last letter from $M$ to $M-1$ still gives a word heavier than $A_i$. In particular $Q_i(1)\ge2$. Its degree is $|A_i|+M$, so $\deg P=N+M$. Formula (1) shows that *every permutation of the gaps*, including the ends, preserves the entire rank polynomial. The recurrence is the maximal-part identity also used by Zhang and Zhang. [Formal block identities](MaximalBlocks.lean) · [Zhang and Zhang](https://arxiv.org/abs/2611.28619)

At least half of the $m+1$ gaps have length at most $2/\delta$, since their lengths sum to $k-m$. Only finitely many different words have such length. Consequently some gap type occurs at least $c(m+1)$ times for a constant depending only on $M,\delta$. Put these copies first. Each product $P_j$ now contains at least $c j$ copies of the same polynomial from a fixed finite set. Let $d$ be the larger of $2+\lceil\log(m+2)\rceil$ and the maximum of $\deg Q_i$. Then $d$ is bounded by a fixed power of $2+\log m$. All estimates below are uniform over the hosts in the theorem.

## Local estimates for products with varying factors

For a nonzero polynomial $T$ with nonnegative coefficients and $t>0$, let $X_{T,t}$ have mass $[x^s]T\,t^s/T(t)$ at the integer $s$. Products add independent variables. Write $\mu_T(t)$ and $V_T(t)$ for its mean and variance. Differentiating with respect to $\log t$ gives $d\mu_T/d\log t=V_T$. Throughout a fixed compact subinterval of $(0,\infty)$, each member of the finite repeated family has variance bounded below. Its characteristic function is bounded in modulus by $e^{-c_1\theta^2}$ for $-\pi\le\theta\le\pi$. This follows from two adjacent positive masses, uniformly bounded below after tilting, by expanding the modulus squared. The constants can be chosen for the whole finite family.

For $T=B_jP_j$ or $P_j$ and $j\ge c_2m/d$, the variance $V$ satisfies $c_3j\le V\le (j+1)d^2$. The same holds for $T=P$ with $j=m+1$. For $|\theta|d$ sufficiently small, the logarithm of the centered characteristic function has expansion

```math
-V\theta^2/2-iK_3\theta^3/6+O((j+1)d^4\theta^4), \tag{2}
```

where $K_3$ is the sum of the third centered moments. This follows by expanding each bounded factor and its logarithm, with $|K_3|\le(j+1)d^3$. On $|\theta|\le(\log m)/\sqrt j$ all errors in the Gaussian approximation tend to zero, with size at most a fixed power of $d$ divided by $\sqrt j$. Outside this arc, the repeated factors bound the absolute integral by $O(e^{-c_4\log^2 m})$. After setting $y=\sqrt V\theta$, Fourier inversion therefore gives

```math
\Pr(X_{T,t}=r)=(1+o(1))/\sqrt{2\pi V}
\qquad \text{if } |r-\mu_T(t)|\le 2d+2. \tag{3}
```

The same estimate holds at $r+1$ in that range after enlarging the constant. A concentration estimate used below is $\Pr(|X-\mu|\ge u)\le2\exp(-c u^2/((j+1)d^2))$. Indeed, the log moment generating function of a centered variable in an interval of width $d$ is zero with zero derivative at zero, and its second derivative at every real tilt is a variance at most $d^2$. Integrate twice, add the bounds for independent factors and optimize the exponential Markov inequality.

## Ranks below the central peak

Let $\rho\in(0,1)$ satisfy $S(\rho)=1$ and fix $t_0=(1+\rho)/2$. Write $\Lambda(t)=\mu_P(t)$. The first-half theorem gives weak increase up to the midpoint of the host weight. We prove positive forward differences for integers $r\ge\lfloor N/2\rfloor$ with $r\le\Lambda(t_0)$. Choose $t=\rho$ if $r\le\Lambda(\rho)$ and otherwise choose $t\in[\rho,t_0]$ so $\Lambda(t)=r$. The latter exists by strict increase. [First-half theorem](../principal-pattern-rank-unimodality/FirstHalf.lean)

On this interval $Q_i(t)\ge1$ and $B_i(t)/Q_i(t)$ lies between a positive constant and $O(d)$. The lower bound follows from $B_i(t)\ge1$ and $Q_i(t)=1+(S(t)-1)B_i(t)$. At $\rho$ the total mass of all words of a fixed length is one, since $\sum_{h=1}^M\rho^h=1$, so $B_i(\rho)\le1+\operatorname{length}(A_i)$. For $t-\rho\le1/d$ the ratio of evaluations of $B_i$ is bounded by $(t/\rho)^d=O(1)$. Otherwise $B_i(t)/Q_i(t)\le1/(S(t)-1)=O(d)$. In particular $B_j(t)P_j(t)\le O(d)P(t)$ for every $j$.

Call a summand $T=B_jP_j$ close if $|r-\mu_T(t)|\le 2\sqrt{m+1}\,d\log m$. For all other summands, (3)'s concentration bound gives total absolute contribution to $t^{r+1}([x^{r+1}]-[x^r])F_W$ of at most $O(md)P(t)e^{-c_5\log^2 m}$. Each close summand has $j\ge c_6m/d$, since $r\ge N/2-1\ge mM/2-1$ and its degree is at most $(j+1)d$. Its tilt can be adjusted to $t_j=t\exp(o(1))$ so that $\mu_T(t_j)=r$. Indeed on a slightly larger compact tilt interval its variance is at least $c_3j$, and the required change in $\log t$ is $O(d^2\log m/\sqrt m)$. By (3) the ordinary coefficient ratio at $r+1$ and $r$ is $(1+o(1))/t_j>1$ uniformly. Thus all close terms contribute positively.

For $t=\rho$ all prefix products have mass one. The successive means $\mu_{P_j}(\rho)$ start at zero, increase by at most $d$, and end at $\Lambda(\rho)$ when the final factor is included. One index $0\le j\le m$ has $|r-\mu_{B_jP_j}(\rho)|\le 2d$ by choosing the prefix immediately before a crossing. If $t>\rho$, the last term has mean within $d$ of $\Lambda(t)=r$ and mass at least a fixed positive multiple of $P(t)$. In both cases a summand within $2d$ has mass at least a fixed multiple of $P(t)$. At the original tilt, (3) gives for this term a positive scaled forward difference of size at least $c_7P(t)/(d\sqrt m)$, since $1-t\ge1-t_0$. It exceeds the entire error from remote summands. This proves the claimed increase.

## The remaining ranks

The universal upper-tail theorem gives weak decrease from $\lfloor(N+k-1)/2\rfloor$. For all ranks between $\Lambda(t_0)$ and this endpoint there is a $t\in[t_0,R]$ with $\Lambda(t)=r$, with $R>1$ fixed uniformly. To see this, $\log P(1)=O(m)$ follows from $Q_i(1)\le M(M+1)^{\operatorname{length}(A_i)}$ and $k\le m/\delta$. The top coefficient of $P$ is at least one. Convexity of $u\mapsto\log P(e^u)$ gives $\deg P-\Lambda(R)\le\log P(1)/\log R$. The distance of the upper-tail endpoint from $\deg P=N+M$ is at least $(N-k)/2\ge (M-1)m/2$. Thus a sufficiently large constant $R$ works. The saddle argument that follows also applies to every integer near $\Lambda(1)$, whether or not it lies inside this interval. [Upper-tail proof](PEAK.md) · [Lean upper tail](BoxProfiles.lean)

Near the positive real axis use $F_W=(P-1)/(S-1)$. Write $b(z)=1/(S(z)-1)$. On a fixed small arc about the positive axis $b$ and its first few derivatives are uniformly bounded for $t\in[t_0,R]$, and $b(t)$ is positive and bounded away from zero. There $P(t)\ge(1+c_8)^{m+1}$ because every $B_i(t)\ge1$. On the rest of the circle use the positive sum in (1). The terms with $j<m/2$ have total evaluation at most $O(m)P(t)(1+c_8)^{-m/2+1}$, by $B_j(t)/Q_j(t)\le1/(S(t)-1)$. Each other term has at least a linear number of the repeated factors. Thus their normalized integral outside $|\theta|\le(\log m)/\sqrt m$ is $O(m e^{-c_9\log^2 m})$. This argument also covers circles passing through complex zeros of $S-1$.

At an integer saddle $r=\Lambda(t)$, denote $a_r=[x^r]F_W$ and $V=V_P(t)$. Inversion with (2) and $b(te^{i\theta})=b(t)+O(|\theta|)$ gives $t^ra_r/P(t)=(b(t)+o(1))/\sqrt{2\pi V}$. In the difference of consecutive *tilted* coefficients the multiplier is $e^{-i\theta}-1$. Its leading term $-i\theta$ integrates to zero against the even Gaussian times $b(t)$. The remaining contributions have integrand bounded by a constant times $(\theta^2+m d^3|\theta|^4+m d^4|\theta|^5+m^2 d^6|\theta|^7)e^{-V\theta^2/2}$ on the inner arc, up to a fixed constant on the Gaussian bound. These terms follow by retaining the cubic term in (2), and bounding the remainder and its square. Integration and $V\ge c_{10}m$ give

```math
\frac{t^{r+1}a_{r+1}-t^ra_r}{P(t)}=O(d^8 V^{-3/2}). \tag{4}
```

Hence the ordinary forward difference has the sign of $1-t$ whenever $|1-t|>C_{11} d^8/m$ for a fixed sufficiently large $C_{11}$. If $|1-t|\le C_{11}d^8/m$, then $|r-\Lambda(1)|\le C_{12}d^{10}$ by integrating the variance upper bound. In this central interval, set $t=1$ and use the multiplier $2\cos\theta-2$ for $a_{r+1}-2a_r+a_{r-1}$. After scaling by $\sqrt{V_P(1)}$, the leading integral is $-b(1)P(1)/(\sqrt{2\pi}\,V_P(1)^{3/2})$. The factor $e^{-i(r-\Lambda(1))\theta}$ tends uniformly to one on the inner arc, since $d^{10}\log m/\sqrt m\to0$. All remainder terms are smaller than the leading term by (2). Consequently the forward differences strictly decrease through this interval, including its adjoining integer ranks after enlarging the fixed constant. The established lower and upper signs and the two outer weak tails now prove unimodality.

## The rank statistic

Put $V=V_P(1)$, and let $K_3$ be the sum of the third centered moments of the normalized $Q_i$ at one. For the weight $X$ of a uniformly chosen distinct subword, (1) gives

```math
\mathbb E X=\Lambda(1)-\frac{S'(1)}{M-1}+o(1),\qquad
\operatorname{Var}X=V+O(1),\qquad
\frac{X-\mathbb E X}{\sqrt V}\ \Longrightarrow\ \mathcal N(0,1).
```

Indeed the first two derivatives of $\log(P-1)-\log(S-1)$ in $\log t$ at zero tilt differ from those of $\log P-\log(S-1)$ by exponentially small quantities times polynomials in $m,d$. For the limit use (2) with $\theta=y/\sqrt V$ for fixed $y$; the cubic error is $O(d^3/\sqrt m)$ and $b(e^{i\theta})/b(1)\to1$.

Every mode has distance at most $1/2+o(1)$ from

```math
\Theta=\Lambda(1)-\frac{S'(1)}{M-1}-\frac{K_3}{2V}.
```

For $|s|=|r-\Lambda(1)|\le C_{12}d^{10}+3$, the first-difference expansion at one, divided by $P(1)b(1)/(\sqrt{2\pi}V^{3/2})$, is $-s+b'(1)/b(1)-1/2-K_3/(2V)+o(1)$. The even contributions come from the quadratic term in $e^{-i\theta}-1$, the linear terms in $e^{-is\theta}b(e^{i\theta})$, and the cubic term in (2). The Gaussian fourth moment is three times the square of its variance. All omitted terms after normalization are at most a fixed power of $d$ divided by $\sqrt m$ by the same expansion. This gives the signs immediately on either side of the candidate ranks. Strict central concavity and the already proved unimodality then give the assertion about *every* mode. At most two adjacent ranks can be modes. For varying hosts the correction can approach a half-integer without coinciding with it. ∎
