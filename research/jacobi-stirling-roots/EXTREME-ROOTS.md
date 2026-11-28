# Uniform simple real roots at the origin end of every deletion row

Let $k\ge1$, $0\le i\le k$, $D=2k-i$, and $p=i/k$. Let $A_{k,i}$ be the numerator in Gessel, Lin and Zeng’s Conjecture 15, including its zero at the origin. For every $j\ge1$ with $16j^2\le k$, its open disk of radius $r_j=\exp(-D/j)$ contains exactly $j$ zeros with multiplicities. Its boundary has no zero. All the zeros in these disks are simple, and every nonzero one is negative. In particular every deletion column has at least $\lfloor\sqrt{k}/4\rfloor-1$ distinct negative zeros. This includes deletion counts proportional to $k$. [Source conjecture](https://arxiv.org/pdf/1201.0622v2) · [Previously proved deletion families](https://arxiv.org/abs/2610.03111)

For $j\ge1$ and any $i=i(k)$, the $j$-th nonzero root in order of increasing modulus, denoted $\zeta_j$, has the following asymptotic, uniformly for $j=o(\sqrt{k})$:

```math
-\zeta_j\sim
\left(\frac{j}{j+1}\right)^D\frac{C_j(p)}{C_{j+1}(p)},\qquad
C_n(p)=\prod_{h=1}^{n-1}\frac1{(1-h/n)(1+(1-p)h/n)}.
```

The proofs below determine the roots in a growing neighborhood of the origin on the natural exponential scale. The conjecture asks about every root. Durán obtains rightmost-root equivalents for classical Bell and Eulerian polynomials. Here the input is a two-parameter Jacobi–Stirling numerator whose real-rootedness is open, and both the root index and deletion count may vary. [Durán](https://arxiv.org/abs/2404.03249)

## A uniform coefficient comparison

Write $c_n=[z^i]h_k(1(1+z),2(2+z),\ldots,n(n+z))$. The ordinary recurrence for Jacobi–Stirling numbers gives this complete homogeneous symmetric function for $\mathrm{JS}(n+k,n;z)$ by expanding $\prod_{h=1}^{n}(1-h(h+z)v)^{-1}$ in $v$. The source generating function is

```math
\sum_{n\ge1} c_n t^n=\frac{A_{k,i}(t)}{(1-t)^{3k-i+1}}.
```

For $n\ge1$ put $B_n=c_n/[\binom{k}{i}n^D]$. Then

```math
(1-2n^2/k) C_n(p)\le B_n\le C_n(p),\qquad
1\le C_{n+1}(p)/C_n(p)\le e .
```

To prove the first two bounds, fix multiplicities of the indices $1,\ldots,n-1$ in a weakly increasing $k$-tuple. Let $M$ be their sum. When $M\le k$ the other $k-M$ indices equal $n$. With $x=h/n$, each position at index $h$ contributes $x[x+(1-x)\mathbf{1}_{\{\text{position deleted}\}}]$ to the normalized summand, averaged over uniformly chosen $i$-subsets. Positions at $n$ contribute one. Expand each of the other positions as either its constant $x^2$ or its marked term $x(1-x)\mathbf 1$. If a term marks a specified set of $l$ positions, the probability it survives is $(i)_{\underline l}/(k)_{\underline l}$ for $l\le i$, and zero otherwise. Each falling factorial here has $l$ factors.

First replace this probability by $p^l$ and remove the bound on $M$. Each level $h<n$ then contributes a geometric series of ratio $q_h=x[x+p(1-x)]$. Their product equals $C_n(p)$. In the associated probability distribution the multiplicities $M_h$ are independent geometric random variables on the nonnegative integers with successive weight ratio $q_h$. Conditionally on these multiplicities, each position at $h$ is independently marked with probability $p(1-x)/(x+p(1-x))$. Write $L_h$ for their number and $L=\sum_hL_h$. Restoring the uniform fixed-size subset gives the exact comparison

```math
B_n/C_n(p)=\mathbb E[\mathbf1_{M\le k} R_L],\qquad
R_l=\frac{(i)_{\underline l}}{(k)_{\underline l}p^l}\quad(0\le l\le i).
```

For $p>0$ set $R_l=0$ when $l>i$. At $p=0$ the independent model marks no position and $R_0=1$. For $p>0$, $0\le R_l\le1$ and $1-R_l\le l(l-1)/(2i)$. Indeed each ratio factor with $0\le h<l\le i$ is $(1-h/i)/(1-h/k)\ge1-h/i$; the product is at least $1-\sum h/i$. For $l>i$ the same bound is immediate. Since $q_h\le h/n$, $\mathbb E M\le n^2$. The independent thinnings $L_h$ are geometric: their probability generating functions are $(1+\mu_h(1-z))^{-1}$ with $\mu_h=p x/(1+(1-p)x)\le p$. Thus $\mathbb E[L(L-1)]=(\sum\mu_h)^2+\sum\mu_h^2\le2p^2n^2$. Markov’s inequality for $M$ and the bound on $1-R_L$ show $1-B_n/C_n(p)\le n^2/k+p^2n^2/i\le2n^2/k$. For $p=0$ only the first summand is needed.

The factors $q_h$ increase with $x$. Comparing level $h$ with level $h+1$ at size $n+1$ gives $C_{n+1}\ge C_n$. The factors $(1-h/n)^{-1}$ alone have product $n^{n-1}/(n-1)!$ and successive ratio $(1+1/n)^n\le e$. The remaining product $\prod(1+(1-p)h/n)^{-1}$ is nonincreasing, by the same index pairing and the new level at $h=1$. This proves the upper ratio bound.

## Counting all zeros inside each circle

At $|t|=r_j$, compare all terms to $c_j r_j^j$. The coefficient estimate gives $B_j\ge C_j/2$ if $16j^2\le k$. For $n\ne j$ the relative absolute contribution is at most

```math
2\exp\!\left((n-j)_+-D\,[n/j-1-\log(n/j)]\right).
```

For $n=j+h$, $h\ge1$, integrate $v/(1+v)$ from zero to $h/j$ to bound the bracket below by $h^2/(2j(j+h))\ge h/(4j^2)$. For $n=j-h>0$ the corresponding bound is $h^2/(2j^2)$. Since $D\ge k\ge16j^2$, summing both tails gives a relative total bounded by $2/(e^3-1)+2/(e^8-1)<1$. The series converges on the closed disk. Rouché’s theorem gives exactly the $j$ zeros of the dominant monomial counted with multiplicity. The denominator has no zero there. The source numerator has a simple zero at zero since $c_1=\binom{k}{i}>0$. Two successive circles therefore enclose one additional zero, which must be simple and real by conjugation. All $c_n$ are positive, so the zero is negative.

## Location of a growing number of zeros

Put $a_j=\log(1+1/j)$ and $R=c_j/c_{j+1}$. For $j=o(\sqrt k)$ the coefficient comparison gives $R=e^{-Da_j}(C_j/C_{j+1})(1+O((j+1)^2/k))$. In particular $R/e^{-Da_j}$ stays between $1/(2e)$ and $2$, uniformly in $i$. The difference $a_j-a_{j+1}=\log(1+1/(j(j+2)))$ is at least $1/(j+1)^2$ by $\log(1+u)\ge u/(1+u)$.

At $|t|=R(1+v)$, $|v|\le1/2$, divide by $c_j|t|^j$. Terms with indices $j+1+h$, $h\ge1$, are smaller than a fixed constant times $[C\exp(-D/(j+1)^2)]^h$ with an absolute $C$. Indeed the successive log slopes of $n^D$ after index $j+1$ are at most $Da_{j+1}$, the factors $C_n/C_{j+1}$ are at most $e^h$, and $B_{j+1}\ge C_{j+1}/2$. The lower tail $j-h$ obeys the same estimate using slopes at least $Da_{j-1}$ when $j>1$ and $C_{j-h}\le C_j$. There is no lower tail if $j=1$. Thus all terms except $j,j+1$ contribute $O(\exp(-D/(j+1)^2))$. At the negative point $t=-R(1+v)$ the central two terms contribute exactly $(-1)^{j+1}v$ in this normalization. Taking $v=\pm\exp(-D/(2(j+1)^2))$ gives opposite signs for all sufficiently large $k$.

Finally $a_j$ differs from both $1/j$ and $1/(j+1)$ by at least $1/(2(j+1)^2)$. This follows by integrating $1/x$ on $[j,j+1]$ and bounding the magnitude of its derivative below by $1/(j+1)^2$. Thus these two test points lie in the annulus between $r_j$ and $r_{j+1}$, which contains exactly one zero. This proves the stated asymptotic.

## What Lean checks

The declaration `JacobiStirlingExtreme.eventual_distinct_negative_roots` constructs an injection from $\{0,\ldots,J-1\}$ into the negative zeros for every sufficiently large $k$ and every $i\le k$. Its hypotheses consist only of the requested number of roots and the deletion range. The proof defines the complete homogeneous polynomial by summing over multiplicities of the letters $h(h+z)$ and evaluates the source numerator by its defining generating series. [Lean source](ExtremeRoots.lean) · [Source definitions](https://arxiv.org/pdf/1201.0622v2)

The formal argument uses a coarser coefficient bound that avoids complex analysis. At $t=-[(2j-1)/(2j+1)]^D$ the $j$-th term eventually dominates both tails uniformly in $i$. The sum on each side of that term has absolute value at most a third of its magnitude. Consecutive test points have opposite signs, and continuity gives a distinct zero between each pair. The exact annulus counts and the asymptotic formula above use the sharper estimates in the written proof.
