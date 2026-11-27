# The raw counts as an expectation over independent gaps

Use the parameters $a,b,c$ from the [conjecture](README.md). Let $U,V,G_1,G_2,\ldots$ be independent rate-one gamma variables of respective shapes $a+c+1$, $b+c+1$, and $c$ for every $G_t$. The original counts satisfy, for every $r\ge1$,

```math
 A_r=\frac{1}{(a!b!)^r}\,
 \mathbb E\prod_{i=1}^r
 \left(U+\sum_{t<i}G_t\right)^a
 \left(V+\sum_{i\le t<r}G_t\right)^b .
```

In the first sum $1\le t<i$. The zeroth term is the empty product, $A_0=1$. For example $A_1=\binom{2a+c}{a}\binom{2b+c}{b}$.

To derive the identity, write $j=r+1$ and fix an interval of length $L$. Assign coordinates $0<y_0<\cdots<y_j<L$ to the successive window endpoints. Each window contributes a chain of $a$ entries below $y_i$, one of $c-1$ entries between $y_i$ and $y_{i+1}$, and one of $b$ entries above $y_{i+1}$. Integrating those chains produces
```math
\prod_{i=0}^{j-1}\frac{y_i^a(y_{i+1}-y_i)^{c-1}(L-y_{i+1})^b}{a!(c-1)!b!}.
```
After integrating in the $y$'s this equals $N(j)L^{1+jd}/(1+jd)!$, since each linear extension occupies a simplex of that volume. Here $d=a+b+c$. Integrating in $L$ against $e^{-L}\,dL$ recovers $N(j)$. All integrands are nonnegative.

Change variables to the two exterior lengths $X=y_0$, $Y=L-y_j$ and the gaps $T_i=y_i-y_{i-1}$ for $1\le i\le j$. The Jacobian is one and the exponential splits. Now $X,Y$ have independent rate-one exponential densities and each $T_i$ has the independent rate-one gamma density of shape $c$. The factor $X^a/a!$ from the first window changes the shape of $X$ to $a+1$. The last window changes the shape of $Y$ to $b+1$. For $j\ge2$, $T_1$ occurs in every remaining left partial sum and in none of the right ones. The analogous statement holds for $T_j$ on the right. Adding these independent variables gives $U=X+T_1$, $V=Y+T_j$ with the stated shapes, and the surviving inner gaps are $G_1,\ldots,G_{r-1}$. This proves the formula. [Source order-polytope calculation](https://arxiv.org/html/2611.12829v1#S8.SS1)

The factors in the product depend on their positions and on $r$. The expectation supplies the raw counts and their factorial normalization. A single positive variable with all the required moments is still needed.

## An obstruction to removing the total gap length

The total $U+V+G_1+\cdots+G_{r-1}$ has shape $K+1+cr$. Its proportions have a Dirichlet law independent of the total. Removing the radial moment gives the candidate compact sequence
```math
 B_r=A_r(a!b!)^r\frac{(cr+K)!}{(dr+K)!}.
```
For $a=b=1,c=3$ the first raw terms are $1,25,2100$. The normalized terms are $1,5/22,5/104$, with $B_0B_2-B_1^2=-45/12584$. Thus simply taking Dirichlet proportions cannot supply the desired compact positive factor. This calculation concerns the normalization above. A normalization with $(cr+c)!$ in its numerator, which the authors use at endpoint distance two, has different Hankel determinants. [Section 8.2](https://arxiv.org/html/2611.12829v1#S8.SS2)
