# Fixed height and translated minors for unsubdivided strips

Fix the height $m\ge2$ of an unsubdivided shifted grid. Let $A_r=g_{m,r+2}$ as in the [strip correspondence](LARGE-HEIGHT.md). Put $R=m^m$ and $\gamma=(m^2-1)/2$.

**Theorem.** There is a constant $C_m>0$ such that $A_r/(R^r r^{-\gamma})$ has an asymptotic expansion to every order in $1/r$ with leading coefficient $C_m$. If $a_0<\cdots<a_{k-1}$ and $b_0<\cdots<b_{k-1}$ are fixed nonnegative integers, then

```math
\det[A_{n+a_i+b_j}]
\sim C_m^k R^{kn+\sum_i(a_i+b_i)}
 n^{-k\gamma-k(k-1)}\,
 \Delta_+(a)\Delta_+(b)\prod_{t=0}^{k-1}\frac{(\gamma)_t}{t!},
\qquad \Delta_+(a)=\prod_{i<j}(a_j-a_i).
```

Here $(\gamma)_t$ is the rising factorial. Hence every fixed translated minor, including every fixed-size adjacent minor, is eventually positive at each grid height. This concerns large moment indices at a fixed height. The [earlier minor result](LARGE-HEIGHT.md) concerns fixed indices at large height.

## Before and after the first activation of all rows

Write a tableau as its word of row numbers. Its row counts lie in $[0,w]$, where $w$ is the common row length. Interior positive counts below $w$ must be strictly decreasing. A string of initial completed rows and a string of final unstarted rows are allowed. Reversing the word and replacing each letter $i$ by $m+1-i$ preserves these rules.

Consider legal prefixes ending on the first appearance of row $m$, temporarily with no upper bound on row lengths. A prefix $P$ of length $K$ ends at a strictly decreasing vector $x_1>\cdots>x_m=1$. The first $K-1$ letters have at most $m-1$ choices. With $\Delta(x)=\prod_{i<j}(x_i-x_j)$, the series

```math
B_m=\sum_P m^{-|P|}\Delta(x(P))
```

is finite, since the Vandermonde is polynomially bounded in $|P|$, and positive, since the staircase of progress values $(m,m-1,\ldots,1)$ can be reached on first starting the last row. Define a reversed terminal prefix $Q$ in the same way, with length $L$ and progress $z$. Once $P,Q$ are specified and $K+L<w$, the endpoints of the middle word are $x$ and $y_i=w-z_{m+1-i}$. They are strictly decreasing and have all coordinates between 1 and $w-1$. Its permitted steps increment one coordinate and stay in the strict chamber. Monotonicity ensures that no endpoint exceptions occur in the middle.

The reflection principle gives the exact middle count

```math
T_w(x,z)=(mw-K-L)!\det\left[\frac1{(w-z_{m+1-j}-x_i)!}\right]_{i,j=1}^m.
```

Indeed, expand the determinant with the above common numerator to count signed unrestricted paths with permuted starting coordinates. Reflect the portion before the first coordinate equality by transposing the first pair reaching equality, breaking any ties lexicographically. This pairs colliding paths with opposite signs. Ordered distinct starts and ends force any surviving path to use the identity. The reciprocal factorial is zero for negative arguments.

## A uniform expansion of the chamber count

Write $b_j=z_{m+1-j}$, $M=m(m-1)/2$ and $x_i=\lambda_i+m-i$. The $\lambda_i$ form a partition of $K-M$. Factor $1/(w-b_j)!$ from column $j$. The resulting determinant of falling factorials is $\Delta(z)$ times the factorial Schur polynomial $s_\lambda(w-b_1,\ldots,w-b_m\mid 0,1,2,\ldots)$, with the first shift equal to zero. Its tableau formula is a sum over semistandard tableaux of shape $\lambda$ with entries in $[m]$. A box in row $i$, column $l$ with entry $t$ contributes $w-b_t-(t+l-i-1)$. The number of tableaux is $\Delta(x)/\prod_{h=1}^{m-1}h!$ by the Weyl dimension formula. [Factorial alternant and tableau formulas, Macdonald, §4](https://www.mat.univie.ac.at/~slc/s/s28macdonald.pdf) · [Molev and Sagan, §§1–2](https://users.math.msu.edu/users/bsagan/Papers/Old/lrr-pub.pdf)

After pulling out leading powers, the contribution of each tableau has a correction factor equal to

```math
\frac{\displaystyle\prod_j\prod_{u=0}^{b_j-1}(1-u/w)
\prod_{(i,l)\in\lambda}\big(1-(b_t+t+l-i-1)/w\big)}
{\displaystyle\prod_{u=0}^{K+L-1}(1-u/(mw))},
\qquad t=T(i,l).
```

The product has constant term one as a function of $1/w$. It has $O_m(K+L+1)$ factors whose coefficients are $O_m(K+L+1)$. On a complex disk of radius $c_m/(1+K+L)^2$ in the variable $1/w$, the absolute value of the product is bounded by a constant depending only on $m$. This follows by summing the bounds for $\lvert\log(1-u/w)\rvert$ on a disk avoiding all denominator zeros. Cauchy's estimates bound the coefficient of degree $t$ by $O_{m,t}((1+K+L)^{2t})$, and give the same type of bound for the Taylor remainder on the disk of half that radius. In particular, uniformly for $K,L$ at most a fixed multiple of $\log w$,

```math
T_w(x,z)=\frac{(mw)!}{(w!)^m}\,w^{-M}
\frac{m^{-K-L}\Delta(x)\Delta(z)}{\prod_{h=1}^{m-1}h!}
\left(1+O_m\left(\frac{(1+K+L)^2}{w}\right)\right),
```

and the correction has an expansion to each prescribed order with polynomially bounded coefficients and remainder. The tableau average preserves all these bounds.

Fix the desired order $J$. Words whose first activation or reversed last activation takes more than $L_0$ steps are at most $2m^{mw}(1-1/m)^{L_0}$: one specified letter is absent from the entire initial or final segment. Choose $L_0=c_{m,J}\log w$, rounded up, with $c_{m,J}$ large enough. The exceptional count divided by $(mw)!\,w^{-M}/(w!)^m$ is then $O(w^{-J-1})$ by Stirling's formula. For all remaining prefixes $K+L<w$ eventually and the exact middle formula applies. At each degree the weighted sum of the coefficient bounds over $P,Q$ converges by the geometric tails of prefix counts. With a sufficiently large $c_{m,J}$, extending each coefficient sum to all prefixes also costs $O(w^{-J-1})$ in this normalization. This gives a full expansion with

```math
g_{m,w}\sim\frac{(mw)!}{(w!)^m}\,w^{-M}\frac{B_m^2}{\prod_{h=1}^{m-1}h!}.
```

Stirling's expansion and $w=r+2$ give the asserted expansion for $A_r$, with $C_m=R^2\sqrt m\,(2\pi)^{(1-m)/2}B_m^2/\prod_{h=1}^{m-1}h!$.

## The minor at large translation

Remove the exponential factors $R^{n+a_i+b_j}$ by row and column scalings. Expand the remaining entry as a power series asymptotically in $1/n$ after extracting $C_m n^{-\gamma}$. At order $u$, the coefficient is a polynomial of degree at most $u$ in $a_i+b_j$. Its top coefficient is $(-1)^u(\gamma)_u/u!$. The other terms in the sequence expansion have degree strictly smaller at this order.

Take divided differences on the first $p+1$ row nodes and the first $q+1$ column nodes for $p,q=0,\ldots,k-1$. These triangular transformations divide the determinant by $\Delta_+(a)\Delta_+(b)$. All terms of order less than $p+q$ vanish, since a monomial must have row degree at least $p$ and column degree at least $q$. At order $p+q$ the surviving coefficient is $(-1)^{p+q}(\gamma)_{p+q}/(p!q!)$. The finite node sets permit the use of the expansion through order $2k-2$ with smaller remainder. Extracting $n^{-p}$ from row $p$ and $n^{-q}$ from column $q$ gives a constant limiting determinant. The signs cancel. Factoring $(\gamma)_p$ from row $p$ leaves the monic polynomials $(\gamma+p)_q$ in $p$, whose determinant is $\prod_{t=0}^{k-1}t!$. Restoring all factors proves the formula.

The remaining positivity question includes unbounded minor orders at small starting indices. This asymptotic does not supply a representing measure.
