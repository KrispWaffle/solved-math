# Largest roots across all deletion counts

For every fixed $J$, all sufficiently large $k$, and every $0\le i\le k$, the $J$ roots of largest modulus of the Jacobi–Stirling numerator $A_{k,i}$ are simple and negative. In order of decreasing modulus they satisfy, uniformly over the whole row,

```math
t_j=-\frac{k(k+r)}{j(j+r)}(1+o(1)),\qquad 1\le j\le J .
```

For $0<i<k$ choose $r$ by $\sum_{h=1}^k r/(h+r)=i$. Interpret the formula at $i=0$ with $r=0$ and at $i=k$ by its limit as $r\to\infty$. Thus the largest root has magnitude asymptotic to $k^2$ at one edge of the deletion row and $k$ at the other. The result also covers, for example, deletion counts on the order of $\log k$, where the relative locations of the largest roots change. [Source conjecture](https://arxiv.org/pdf/1201.0622v2) · [Reciprocal identity and proof for proportional deletion counts](LARGE-ROOTS.md)

## The two limiting functions

Keep $Q(u)=u^{2k-i}A_{k,i}(1/u)$ and $m=3k-i$. Use $\tau=(1+r)/(k(k+r))$ with $\tau=1/k$ at $r=\infty$. Along every sequence on which $r\to R<\infty$, locally uniformly in complex $y$,

```math
Q(\tau y)/Q(0)\ \longrightarrow\
F_R(y)=\prod_{h=1}^\infty
\left(1+\frac{(1+R)y}{h(h+R)}\right).
```

Along every sequence with $r\to\infty$, put $\ell=kr/(k+r)$, extended by $\ell=k$ at $r=\infty$. Then

```math
\frac{\exp((m+1)\tau y)}{\ell^y}\frac{Q(\tau y)}{Q(0)}
\ \longrightarrow\ \frac{1}{\Gamma(1+y)} .
```

The zeros of $F_R$ are the simple points $-j(j+R)/(1+R)$ because the product converges absolutely on compact sets and its factors have distinct zeros. The zeros in the second limit are the simple negative integers. In either case, take a disk containing precisely the first $J$ limiting zeros and separate them with smaller disks. Rouché's theorem and conjugation give the asserted number, simplicity, reality and locations of the reciprocal roots. Every sequence of deletion counts has a subsequence on which $r$ converges in $[0,\infty]$. Applied to a hypothetical sequence violating the conclusion, this gives uniformity over $i$. [Reciprocal gamma zeros](https://dlmf.nist.gov/5.8.E2)

## The product at the coefficient saddle

Use $B_s(z)$ from the reciprocal identity. For $u=\tau y$ the exact expression for $u^s B_s(z)/B_0(z)$ is still $[x^s]P(x)H_s(x)$ from the proportional-column proof. It now has

```math
P(x)=\prod_{h\le k}(1+xy v_h(z)),\qquad
v_h(z)=\frac{(1+r)(k+z)}{(k+r)h(h+z)},\qquad
v_h(r)=\frac{1+r}{h(h+r)}.
```

At complex points used below $|k+z|$ is bounded below by a constant multiple of $k+r$. Thus both coefficients $A_1,A_2$ in $H_s$ stay bounded, as does $w=k\tau y$. For bounded $r$, $\sum_h v_h(r)$ is bounded. For $r\to\infty$ one has

```math
T=\sum_{h\le k}v_h(r)
=(1+1/r)\left(\sum_{h\le k}1/h-\sum_{h\le k}1/(h+r)\right)
=\log\ell+\gamma+o(1).
```

Indeed the second harmonic sum differs from $\log(1+k/r)$ by $O(1/r)$, and $\log\ell/r\to0$ as $\ell\le r$. In all regimes $T=O(1+\log(1+\ell))$ and $0<v_h(r)\le1/h$.

Write $z=r e^{\mathrm i\theta}$. On arcs with $|\theta|=o(1)$ the exact formula

```math
\frac{v_h(z)}{v_h(r)}-1
=\frac{(r-z)(k-h)}{(k+r)(h+z)}
```

has modulus at most $C|\theta|\min(1,k/r)$. If $r\ge2k$ the bound $Ck/r$ holds on the entire circle. If $r\to0$ it is $O(r)$ on the entire circle, since $h\ge1$. We will choose arcs on which $\sum_{h\le k}|v_h(z)-v_h(r)|=o(1)$ uniformly.

For $r\to R<\infty$, dominated product convergence on these arcs gives $P(x)\to F_R(xy)$ for bounded $x,y$. For $r\to\infty$ use instead the product of $(1+xy v_h(z))\exp(-xy v_h(z))$. Its deviations from one are summably bounded by $C/h^2$, and for fixed $h$, $v_h(z)\to1/h$. Using the formula for $T$ to restore the exponential gives $\ell^{-xy}P(x)\to1/\Gamma(1+xy)$, locally uniformly. This argument also controls the product at its zeros.

## Summing the coefficient corrections

The expansion in powers of $1/k$ in the proportional-column proof applies on the chosen arcs. On $|x|=2$ its prefix bound becomes $|P(x)|\le C(1+\ell)^B$ for fixed compact $y$-sets. At $x=1$ the derivatives of fixed order $b$ are bounded in the finite-$R$ regime. For $r\to\infty$ they are $O_b(\ell^{\operatorname{Re}y}(1+\log\ell)^b)$ by the circle of radius $1/(1+\log\ell)$ around one. Thus every nonconstant order in the expansion divided by the target scale tends to zero. The Taylor remainder of order $L$ is $O_L((1+\ell)^B/k^{L+1})$, and $\ell\le k$ allows a single sufficiently large $L$ for each compact set.

For completeness, the exact terms with $(\log k)^2<s<\eta k$ still decay at least as $C(1+\ell)^B e^{-c s}$ by the radius-two estimate on $H_s$. The tail $s\ge\eta k$ at $r$ is $O(\exp(-c k\log k))B_0(r)$ by the binomial bound. On a shrinking arc, $B_0(r)/|B_0(z)|\le\exp(CV\theta^2)$, where $V$ is defined below. On the full circles used below each $p_h(1-p_h)$ tends uniformly to zero, giving the bound $\exp(CV)$ there. Since $V\le k/4$, the large-$s$ tail is negligible on either normalization. These estimates establish the same finite-$R$ or infinite-$r$ limit for $\sum_s u^s B_s(z)/B_0(z)$ as for $P(1)$.

## Recovering the exact coefficient

For $0<i<k$, write $p_h=r/(h+r)$ and $V=\sum_{h\le k}p_h(1-p_h)$. The normalized coefficient $r^i[z^i]B_0(z)/B_0(r)$ is the probability of obtaining the integer mean $i$ for a sum of independent Bernoulli variables with parameters $p_h$. If $V\to\infty$ it is asymptotic to $1/\sqrt{2\pi V}$. Indeed the modulus of the centered characteristic function is at most $\exp(-2V\sin^2(\theta/2))$, and its logarithm at small $\theta$ is $-V\theta^2/2+O(V|\theta|^3)$. The latter bound follows by differentiating $\log(1-p+p e^{\mathrm i\theta})$ three times on $|\theta|\le1/2$, where the third derivative is $O(p(1-p))$. Gaussian integration proves the formula. The integral of the absolute value is $O((1+V)^{-1/2})$ in every case.

If $V$ stays bounded, pass to a subsequence. For $r$ bounded away from both zero and infinity, $V$ grows as a positive multiple of $\log k$. For $r\to\infty$ with $r\le2k$, $V\ge c\ell\to\infty$ by using $h$ between $r/2$ and $r$ when $r\le k$, or between $k/2$ and $k$ otherwise. The bounded-variance cases therefore have $r\to0$ or $r/k\to\infty$ (for $r\ge2k$, $V$ is comparable to $k^2/r$). In the former case take the successes, in the latter the failures. Their maximum individual probability tends to zero, and their integer total mean stays bounded because it is asymptotic to $V$ when it is positive. Take a subsequence with this integer fixed at $b$. The product of their characteristic functions tends uniformly to $\exp(b(e^{\mathrm i\theta}-1))$ by the logarithm expansion and the vanishing sum of squared probabilities. The mass at the mean tends to $e^{-b}b^b/b!$ with value one when $b=0$. In particular the denominator stays bounded away from zero along this subsequence.

On any complementary arc there is a uniform bound for the entire numerator. Each monomial product in $B_s$ omits at most $s$ members of $[k]$. Each omitted index removes at most $1/4$ from the variance sum. The characteristic function modulus bound therefore gives

```math
|B_s(r e^{\mathrm i\theta})|
\le e^{-2V\sin^2(\theta/2)}e^{s/2}B_s(r).
```

The radius-two and tail estimates at the positive point, now with $e^{1/2}|y|$, show $\sum_s e^{s/2}|u|^s B_s(r)/B_0(r)\le C(1+\ell)^B$.

The following choices justify the arcs used in the product estimate and coefficient extraction.

- For $r\le2k$ and $V\to\infty$, take $|\theta|\le\log(2+V)/\sqrt V$. Here $\ell=O(1+V)$ by the interval bound above when $r\to\infty$, and $\ell$ is bounded when $r$ is bounded. The product perturbation is $o(1)$ because $|\theta|(1+\log(1+\ell))\to0$. The complementary bound is exponentially small in $\log^2(2+V)$.
- For $r\ge2k$ and $V>(\log(2+k))^8$, take $|\theta|\le\log(2+k)/\sqrt V$. Again $|\theta|(1+\log(1+\ell))\to0$ and the complementary bound absorbs every fixed power of $k$.
- For $r\ge2k$ and $V\le(\log(2+k))^8$, use the whole circle. The bound $k/r=O(V/k)$ gives $(k/r)(1+\log(1+\ell))\to0$. For $r\to0$ and bounded $V$ use the whole circle as well, with the $O(r)$ perturbation.

Integrate the uniform product estimate against $B_0(r e^{\mathrm i\theta})e^{-\mathrm i i\theta}$. Its error divided by the denominator tends to zero by the absolute integral and the mean-mass estimates. For bounded $r$, $(m+1)\tau\to0$. In all cases $(1-\tau y)^{m+1}\exp((m+1)\tau y)=1+O(1/k)$ on compact sets. The reciprocal identity now proves both limits for $Q$.

At $i=0$ simply evaluate at $z=0$ with letters $h^2$ and $\tau=1/k^2$. At $i=k$ take the leading deletion coefficient, which replaces every letter $h(h+z)$ in the elementary symmetric function by $h$. Here $B_0=k!$, $P(x)=\prod_{h=1}^k(1+xy/h)$ and $H_s(x)=\prod_{j=1}^s(1+(j+yx)/k)$. The same coefficient expansion proves the respective limits directly.

The all-column asymptotics are a written result. Lean checks the exact real generating-series identity used in both regimes. Integer arithmetic independently checks the reciprocal coefficients and the signs at rational arguments across the deletion row. [Lean source](Reciprocal.lean) · [Exact checker](check_reciprocal.py)
