# Asymptotics for repeated labels

Use the corrected band and the notation of the [finite transfer](PROOF.md). Fix the width and the starting and ending outlines. Let $s$ tend to infinity along the admissible diagram sizes and write $f_{s,b}=f^{D_s}(s+b)$. Let $T$ be the ordinary outline adjacency matrix, $\rho$ its Perron root, and $d_x$ the number of reverse-legal bonds at outline $x$. Write $d_*=\max_x d_x$. Every $d_x\ge1$; at width one take $T=(1)$ and $d_x=1$.

**Fixed excess.** For every fixed $b\ge0$,

```math
f_{s,b}\sim f_{s,0}\frac{(\bar d\,s)^b}{b!},
\qquad
\bar d=\frac{\sum_x l_x r_x d_x}{\sum_x l_x r_x},
\qquad l^\mathsf T T=\rho l^\mathsf T,\quad Tr=\rho r .
```

The ordinary count itself is asymptotic to a positive constant times $\rho^s$. The coefficient $\bar d$ is independent of the endpoint outlines. The source uses copies of a zigzag as its size parameter; a complete copy has $w$ cells, so substitute $s=wk$ for equal outlines.

**Positive limiting excess per cell.** Put $F_s(u)=\sum_b f_{s,b}u^b$ and

```math
M(u)=T\,\operatorname{diag}_x(1-u d_x)^{-1},
\qquad K(t)=\log\rho(M(e^t)),\qquad -\infty<t<-\log d_*.
```

Given integers $b_s$ with $b_s/s\to\theta\in(0,\infty)$, there is a unique $t_s$ with $K'(t_s)=b_s/s$ for all sufficiently large $s$. Then

```math
f_{s,b_s}\sim\frac{F_s(e^{t_s})e^{-t_sb_s}}{\sqrt{2\pi s K''(t_s)}} .
```

At fixed positive $u<1/d_*$, $F_s(u)\sim c(u)\rho(M(u))^s$ with an effective positive analytic amplitude given by the transfer and Perron projection below. The saddle formula also permits this replacement at the varying $u=e^{t_s}$.

## When the initial boundary disappears

Let $c_i$ be the number of forward moves at bond $i$. For each site the difference of the counts at its bounding bonds is its final occupation minus its initial occupation, hence has absolute value at most one. The counts at any two bonds differ by at most $w-1$. If any bond is still unused, there have been at most $w(w-1)$ discoveries. Thus after $L=w(w-1)+1$ discoveries, every path has visited every bond, uniformly in its start and in the intervening repeats. At that time the number of repeat choices at outline $x$ is exactly $d_x$.

All ordinary outlines communicate. Starting at an outline, drain its rightmost particles first; to reach any final outline from empty, place its particles rightmost first. At a return all forward counts are equal by particle conservation, so lengths are multiples of $w$. One particle traversing the entire empty system gives a return of length $w$. The period is exactly $w$, including the one-state width-one convention. Hence $T^w$ restricted to any cyclic class is primitive.

At any fixed discovery path, sum the arbitrary repeats before the first discovery, between discoveries and after the last. At a state with $d$ legal repeats this gives $(1-ud)^{-1}$. The initial factor is one. Thus after the first $L$ discoveries all weights are implemented by $M(u)$ above. Their first $L$ factors give a finite initial row vector analytic for $|u|<1/d_*$. At real $0\le u<1/d_*$ the matrix $M(u)$ has the same irreducible support and period as $T$. On each cyclic class the $w$-step Perron root is simple and strictly dominates every other eigenvalue in modulus. Its spectral projection is positive. Any allowed start and terminal residue has positive leading amplitude by accessibility.

More explicitly, for $s=L+r+wk$, $0\le r<w$, multiply the initial row by $M(u)^r$ and the $k$th power of the appropriate primitive block of $M(u)^w$, then select the terminal outline. Replacing that block power by its Perron eigenvalue to power $k$ times its spectral projection gives the amplitude $c(u)$ after dividing by $\rho(M(u))^s$. The simple eigenvalue and its projection continue analytically to a neighborhood of each fixed real $u$ in the stated interval. The complementary block powers are uniformly exponentially smaller on a sufficiently small complex neighborhood, by the spectral gap and a resolvent contour around the remaining eigenvalues. Hence, along the allowed sizes, locally uniformly and with all fixed derivatives,

```math
F_s(u)=c(u)\lambda(u)^s(1+O(q^s)),\qquad
\lambda(u)=\rho(M(u))\ \text{on the real interval},\quad 0<q<1.
```

There is one allowed residue modulo $w$ for a given pair of outlines. Differentiating the simple eigenvalue at zero, where $M'(0)=T\operatorname{diag}(d_x)$, gives $\lambda'(0)/\lambda(0)=\bar d$. The coefficient of $u^b$ in $(\lambda(u)/\lambda(0))^s$ is a polynomial in $s$ with leading term $(s\bar d)^b/b!$; derivatives of $c$ contribute lower powers. The error after taking this coefficient is exponentially smaller by Cauchy's estimate on a sufficiently small circle. This proves the fixed-excess assertion.

## A saddle point for positive excess density

Under weights proportional to $f_{s,b}u^b$, condition on the entire discovery path. The repeats at successive states are independent geometric counts with means $ud/(1-ud)$ and variances $ud/(1-ud)^2$. In particular the second derivative in $t=\log u$ of $\log F_s(e^t)$, the unconditional variance, is at least $(s-L)\min_{1\le d\le d_*}ud/(1-ud)^2$. The analytic approximation above implies $K''(t)>0$. Also $K'(t)\to0$ at the left endpoint by analyticity at $u=0$. At the right endpoint a directed cycle through a state with $d_x=d_*$ has diverging weight product; its geometric mean bounds the Perron root from below. Convexity and divergence of $K$ at a finite endpoint force $K'(t)\to\infty$. These facts give the claimed unique $t_s$, tending to a finite interior value.

For coefficient extraction let $u=e^{t_s}$. Fourier inversion divides $F_s(u)$ by $2\pi u^{b_s}$ and integrates $F_s(ue^{i\phi})e^{-ib_s\phi}/F_s(u)$ over $[-\pi,\pi]$. The characteristic function of a geometric count of parameter $ud$ has magnitude $(1-ud)/|1-ud e^{i\phi}|$. Conditioning on the path therefore bounds the absolute integrand by $\exp(-c s\phi^2)$ on this full interval for sufficiently large $s$, uniformly as $u$ ranges over a small compact neighborhood of its limiting interior value. Indeed $1-\cos\phi\ge 2\phi^2/\pi^2$ there, and at least $s-L$ factors have $1\le d\le d_*$. At $\phi=x/\sqrt{s}$ the analytic Perron approximation and $sK'(t_s)=b_s$ leave the Gaussian factor $\exp(-K''(t_s)x^2/2)$ up to an error tending to zero for bounded $x$. Dominated convergence with the preceding Gaussian bound gives the displayed local asymptotic. The bivariate transfer remains exact at every integer excess, including regimes outside these two asymptotic statements.

## Sparse and very large excess

The same saddle formula holds if $b=b_s$ tends to infinity and $b/s$ tends to zero. In this case $u_s=e^{t_s}\sim b/(s\bar d)$ and $sK''(t_s)\sim b$. To see this, analyticity at zero gives $\log(\lambda(u)/\lambda(0))=\bar d u+O(u^2)$. Applying $u\,d/du$ once or twice gives the same leading term. The third logarithmic derivative is $O(u)$ uniformly on the small complex circles used in inversion. At $\phi=x/\sqrt{sK''(t_s)}$ the cubic Taylor remainder in the exponent is $O(|x|^3/\sqrt b)$, and the analytic amplitude ratio tends to one. The conditional geometric factors give the full-circle bound $\exp(-c s u_s\phi^2)$ for a constant $c>0$, since each interior repeat count lies between one and $d_*$. These estimates again give the Gaussian integral, now on the scale $\sqrt b$.

In particular the simpler equivalent $f_{s,b}\sim f_{s,0}(s\bar d)^b/b!$ holds whenever $b=o(\sqrt{s})$. For unbounded $b$ in this range, the log expansion above gives $s\log(\lambda(u_s)/\lambda(0))=b+O(b^2/s)$ and $b\log(s\bar d u_s/b)=O(b^2/s)$. The amplitude tends to $c(0)$ and Stirling’s formula gives the claimed equivalent. Bounded $b$ is already covered by coefficient extraction.

There is also a growth rate for every sequence with $b/s\to\infty$ as $s\to\infty$ along the prescribed residue. At every outline the reverse-legal bonds form a set of nonconsecutive bonds. In the bit picture they are precisely the transitions $0\to1$ after adjoining boundary bits $0$ and $1$. Alternating the interior bits starting with $1$ realizes the upper bound $d_*=\lceil w/2\rceil$. For all sufficiently large admissible $s$, some discovery path reaches an outline with $d_*$ eligible repeats and then reaches the prescribed end. Indeed take $L$ steps to eliminate the initial flags, connect to a maximizing outline, and complete the path to the fixed endpoint. The support is irreducible of period $w$, so completions exist at every sufficiently large allowed length. Inserting all $b$ repeats there gives at least $d_*^b$ words. Conversely every word comes from at most $w^s$ choices of discovery path, a weak composition of the excess into the $s$ post-discovery positions, and at most $d_*^b$ choices of repeated cells. Thus

```math
d_*^b\le f_{s,b}\le w^s\binom{s+b-1}{s-1}d_*^b,\qquad
\lim_{s\to\infty,\ b/s\to\infty} f_{s,b}^{1/b}=d_* .
```

For the limit use $\binom{s+b}{s}\le [e(1+b/s)]^s$. This gives the exponential rate in very large excess. The saddle equivalents above give more information in the regimes they cover.

## Fixed finite diagram

Fix a nonempty diagram instead, and let only $b$ grow. This statement holds for the same word predicate on any nonempty finite poset. At a discovery path $P$ let $d_j(P)$ be the number of maximal cells after its first $j$ discoveries, $1\le j\le s$. Put $D=\max_{P,j}d_j(P)$, and let $m$ be the largest number of indices with $d_j(P)=D$ on any one path. The integer $D$ is the width of the finite poset. Its maximal cells at any prefix form an antichain. Conversely, the ideal generated by a maximum antichain has exactly that antichain as its set of maximal cells and occurs as a prefix of a linear extension.

The single-diagram series is $\sum_P\prod_j(1-u d_j(P))^{-1}$. All its poles are positive real numbers. Its closest pole is $1/D$, with order $m$ and strictly positive leading coefficient

```math
C=\sum_{P:\#\{j:d_j(P)=D\}=m}\ \prod_{j:d_j(P)<D}(1-d_j(P)/D)^{-1}.
```

Partial fractions give $f_{s,b}\sim C D^b\binom{b+m-1}{m-1}$ as $b\to\infty$. This fixed-poset consequence follows directly from the prefix formula. It supplies a separate boundary check on the growing-period estimates.
