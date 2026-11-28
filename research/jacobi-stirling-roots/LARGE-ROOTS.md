# The largest Jacobi–Stirling roots in proportional deletion columns

Fix $0<\epsilon<1/2$. Write $A=A_{k,i}$ for the numerator in Gessel, Lin and Zeng's Conjecture 15 with its terminal-descent factor. Consider all $\epsilon k\le i\le(1-\epsilon)k$. For every fixed $J$, the $J$ roots of largest modulus are simple and negative for all sufficiently large $k$. In decreasing order of modulus they satisfy

```math
t_j=-\frac{k}{\alpha j}(1+o(1)),\qquad 1\le j\le J.
```

Here $r>0$ is the unique solution of $\sum_{h=1}^k r/(h+r)=i$ and $\alpha=r/(k+r)$. The error is uniform over the indicated columns. If $i/k\to p$ in $(0,1)$, then $r/k\to\lambda$, where $\lambda\log(1+1/\lambda)=p$. Both conclusions follow by monotonicity and Riemann sums. This treats the opposite end from the exponentially small roots. The intervening roots of the source conjecture remain open. [Source, Conjecture 15](https://arxiv.org/pdf/1201.0622v2) · [Small roots](EXTREME-ROOTS.md)

## A limit for the reversed numerator

Put $m=3k-i$, $D=2k-i$, $\sigma=\alpha/k$ and $Q(u)=u^D A(1/u)$, extended at zero. We prove locally uniformly for complex $y$ that

```math
\frac{\exp((m+1)\sigma y)}{(k\alpha)^y}\,
\frac{Q(\sigma y)}{Q(0)}
\longrightarrow \frac{1}{\Gamma(1+y)}.
```

Positive real bases in complex powers use the real logarithm. The limit has simple zeros at the negative integers. On the disk of radius $J+1/2$, use Rouché's theorem on the boundary and on small disjoint circles around $-1,\ldots,-J$. Each small disk contains a single zero with multiplicity and the large disk contains exactly $J$. Complex conjugation makes the single zero in each small disk real. Shrinking the circles gives the stated asymptotics after taking reciprocals. [Weierstrass product for the reciprocal gamma function](https://dlmf.nist.gov/5.8.E2)

## Reversing the source series

Write $a_h(z)=h(h+z)$ and $c(n)=[z^i]h_k(a_1(z),\ldots,a_n(z))$, where $h_k$ is complete homogeneous. For $n\ge0$ this is the Jacobi–Stirling diagonal. It extends to a polynomial in $n$ by the recurrence $h_k(n)-h_k(n-1)=a_n h_{k-1}(n)$ and polynomial summation. Starting with the empty alphabet at zero, the same recurrence run backwards gives

```math
c(-n)=(-1)^{k+i}[z^i]e_k(a_1(z),\ldots,a_{n-1}(z)),\qquad n\ge1.
```

Indeed $H_n(v)=\sum_{k\ge0}h_k(n)v^k$ satisfies $H_{n-1}=(1-a_n v)H_n$. At negative indices its factors use $a_{-h}(z)=a_h(-z)$ and $a_0=0$. For a polynomial $c$, the rational functions $\sum_{n\ge0}c(n)t^n$ and $-\sum_{n\ge1}c(-n)t^{-n}$ agree. This follows on the basis $\binom{n}{j}$ from the negative-binomial series. Substituting the source denominator $(1-t)^{m+1}$ and using $(-1)^m=(-1)^{k+i}$ yields

```math
\frac{Q(u)}{(1-u)^{m+1}}
=\sum_{s\ge0}u^s[z^i]B_s(z),\qquad
B_s(z)=[q^s]\prod_{h=1}^{k+s}\big(a_h(z)+q\big).
```

In particular $Q(0)=[z^i]B_0(z)>0$, which also identifies the degree $D$. The next two steps estimate this series first at a complex value of $z$, then at its exact coefficient.

## Estimating the series near the positive saddle

Let $r$ be as above, $u=\sigma y$, $w=ku=\alpha y$. In every estimate $y$ ranges over a fixed compact set and $r/k$ over a compact subinterval of $(0,\infty)$. Set $z=r e^{\mathrm i\theta}$ with $|\theta|\le(\log k)/\sqrt{k}$. Define

```math
P(x)=\prod_{h=1}^{k}\left(1+\frac{u a_k(z)x}{a_h(z)}\right),\quad
b=\frac{u a_k(z)}{z},\quad
H_s(x)=\prod_{\ell=1}^{s}
\left(1+\frac{A_1\ell+w x}{k}+\frac{A_2\ell^2}{k^2}\right),
```

where $A_1=(2k+z)/(k+z)$ and $A_2=k/(k+z)$. A rescaling of the coefficient variable gives the exact identity

```math
\frac{u^s B_s(z)}{B_0(z)}=[x^s]P(x)H_s(x).
```

It holds also at $u=0$ by polynomial continuation. We claim that summing over $s$ gives $P(1)+o(k^{\operatorname{Re}y})$. The absolute error is important near the zeros.

First, $P$ has the following uniform product asymptotic when $x$ ranges over a compact set.

```math
k^{-bx}P(x)=
\frac{(1+k/z)^{-bx}}{\Gamma(1+bx)}+o(1).
```

To see this write each factor as $1+b x d_h/h$ with $d_h=z/(h+z)$. The compensated factors $(1+b x d_h/h)e^{-b x d_h/h}$ have summable uniform tails bounded by $C/h^2$ in distance from one. For fixed $h$, $d_h\to1$ uniformly. Their product converges to the Weierstrass product with the exponential constant removed. The remaining sum is
$\sum_{h\le k}d_h/h=\sum_{h\le k}1/h-\sum_{h\le k}1/(h+z)=\log k+\gamma-\log(1+k/z)+o(1)$ by a uniform Riemann sum. Use the continuous logarithm near the positive axis. Since $b=y+O(|\theta|)$, Cauchy's derivative bound on $|x-1|=1/\log k$ gives $P^{(j)}(1)=O_j(k^{\operatorname{Re}y}(1+\log k)^j)$ for each fixed $j$. The same product bounds $|P(x)|$ by $Ck^B$ on $|x|=2$ for a constant $B$ depending only on the compact sets.

For the coefficient sum put $S=\lceil(\log k)^2\rceil$. For $s\le S$, replace $1/k$ in $H_s$ by a variable $\delta$ and expand to order $L$. The coefficient $H_{s,h}(x)$ of $\delta^h$ is a polynomial in $s,x$ of bounded degree for each fixed $h$, with uniformly bounded coefficients. Indeed, after choosing the nonconstant factors one sums monomials in at most $h$ ordered distinct indices up to $s$. Repeated power summation gives polynomials in $s$. On $|x|=2$, $|\delta|=1/[C(1+s)^2]$, the product is bounded by an absolute constant for sufficiently large $C$. Cauchy's estimate therefore bounds the discarded remainder at $\delta=1/k$ by $C_L[C(1+s)^2/k]^{L+1}$. After coefficient extraction the total error is $O_L(k^{B-L-1})$, since $\sum_{s\ge0}2^{-s}(1+s)^{2L+2}$ converges.

For $S<s<\eta k$ the exact products on $|x|=2$ obey $|H_s(x)|\le \exp(C(s^2+s)/k)$. Choose a fixed $\eta>0$ small enough that $2^{-s}$ times this bound decays exponentially in $s$. The discarded tail is smaller than every inverse power of $k$. For $s\ge\eta k$, positivity and monotonicity at $r$ give

```math
B_s(r)/B_0(r)
\le \binom{k+s}{k}\prod_{j=1}^k a_{j+s}(r)/a_j(r)
\le \binom{k+s}{k}^3\le 2^{3(k+s)}.
```

Here $(j+s+r)/(j+r)\le(j+s)/j$. Since $|u|\le C/k$, the tail normalized by $B_0(r)$ is superpolynomially small. On the central arc $B_0(r)/|B_0(z)|\le \exp(C k\theta^2)\le\exp(C\log^2 k)$, so the tail from $s\ge\eta k$, of order $\exp(-c k\log k)$, is negligible after either normalization.

Extend each of the finitely many polynomial coefficient sums to all $s$. The extra terms contribute at most $C_L k^B\sum_{s>S}2^{-s}(1+s)^{C_L}$. For a monomial $s^j x^\ell$ in $H_{s,h}$ the extended sum equals
```math
\sum_{s\ge0}s^j [x^s]\big(x^\ell P(x)\big)
=\left.(x\,d/dx)^j\big(x^\ell P(x)\big)\right|_{x=1}.
```
The order-zero term is $P(1)$. Every order $h\ge1$ is bounded by $C_L k^{\operatorname{Re}y-h}(1+\log k)^{C_L}$ by the derivative estimates. Choosing $L>B+\sup|y|+2$ proves the claim. Consequently on the central arc

```math
\frac{\sum_{s\ge0}u^s B_s(z)}{B_0(z)}
=(k\alpha)^y\left(\frac{1}{\Gamma(1+y)}+o(1)\right)
```

uniformly, since $(b-y)\log k=o(1)$ and $(1+k/z)^{-1}=\alpha+o(1)$ there.

## Extracting the deletion count

Set $p_h=r/(h+r)$ and $V=\sum_{h\le k}p_h(1-p_h)$. The indices $k/2\le h\le k$ have $p_h$ bounded away from both zero and one, so $V$ is bounded above and below by positive multiples of $k$. On the central arc,

```math
e^{-\mathrm i i\theta}B_0(r e^{\mathrm i\theta})/B_0(r)
=\exp(-V\theta^2/2+O(k|\theta|^3)).
```

This follows by expanding $\prod_h(1-p_h+p_h e^{\mathrm i\theta})$ and using $\sum p_h=i$. Its integral divided by $2\pi$ is $(1+o(1))/\sqrt{2\pi V}$. The integral of its absolute value on the arc is also $O(k^{-1/2})$.

For the other angles, each product contributing to $B_s$ with $s\le S$ contains at least $k/2-S-1$ factors with $k/2\le h\le k$. The identity $|1-p+p e^{\mathrm i\theta}|^2=1-4p(1-p)\sin^2(\theta/2)$ therefore gives
$|B_s(r e^{\mathrm i\theta})|\le B_s(r)\exp(-c k\sin^2(\theta/2))$. The sum of $|u|^s B_s(r)/B_0(r)$ for $s\le S$ is $O(k^B)$ by the radius-two estimate at positive $r$ and $|y|$. The terms $s>S$ are superpolynomially small in this normalization by the two tail bounds above, now used at $r$. Thus the complementary arc contributes $O(k^{-A})B_0(r)$ for every fixed $A$, for the numerator and denominator alike.

Cauchy's coefficient formula now divides the central-arc estimate by the Gaussian integral for $[z^i]B_0$. The term $o(1)$ stays uniform after integration, by the bound for the integral of the absolute value. Finally $(1-\sigma y)^{m+1}\exp((m+1)\sigma y)=1+O(1/k)$ on compact sets. This proves the limit for $Q$.

## Verification scope

Lean proves the reciprocal series identity for every deletion count and for all nonzero real $t$ with $|t|<1$. Its numerator is the polynomial specified by the original positive-index series. The complex limit and the zero count above are written proofs. An exact checker also compares elementary symmetric functions against the independent descent-insertion recurrence. [Reciprocity in Lean](Reciprocal.lean) · [Source polynomial](SourcePolynomial.lean) · [Exact checker](check_reciprocal.py)
