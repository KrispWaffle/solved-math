# Eventual positivity of fixed Hankel minors in unsubdivided shifted grids

Let $A^{(m)}_r$ be the number of regular packings of $r+1$ occurrences for an unsubdivided shifted grid with $m$ levels. The pattern with odd letters increasing followed by even letters increasing in $S_{2m}$ is one representative. All these counts depend only on the grid poset. The authors identify the poset with the strip of $m$ rows of length $w=r+2$, via the cell coordinates $(i,q+i)$ for $0\le q<w$. Denote its number of standard tableaux by $g_{m,w}$. In particular $A^{(m)}_0=g_{m,2}=1$. [Blitvić, Kammoun and Steingrímsson, §§7, 9.1 and 10](https://arxiv.org/html/2611.12829v1#S7)

**Theorem.** Fix $d\ge1$, and two strictly increasing lists of nonnegative integers $a_1,\ldots,a_d$ and $b_1,\ldots,b_d$. Define $H_m(i,j)=A^{(m)}_{a_i+b_j}$. There are constants $0<q<1$ and $C>0$, depending on these lists, such that for all sufficiently large $m$,

```math
\left|\frac{\det H_m}{\prod_i H_m(i,i)}-1\right|\le Cq^m .
```

In particular $\det H_m>0$ for every sufficiently large $m$. The conclusion allows arbitrary fixed orders, shifts, and nonprincipal minors. A finite collection of tests therefore passes simultaneously for all sufficiently tall unsubdivided grids. Conjecture 10.5 requires every minor at each prescribed height and allows subdivisions.

## Strip counts as returns

For fixed $w\ge2$ let $T_w$ be the adjacency matrix of the following directed graph on subsets of $\{1,\ldots,w-1\}$. A move introduces a particle at site 1 if empty, advances a particle one site into a vacancy, or removes a particle from the last site. This is the open totally asymmetric simple exclusion process with unit edge weights and with the diagonal left at zero. Then

```math
g_{m,w}=(T_w^{mw})_{\varnothing,\varnothing}.
```

Here is the strip specialization of Dal Zovo's tableau–walk correspondence. In a tableau prefix write the number of exposed cells of each row, in order from top to bottom. Each lies between 0 and $w$. If a lower row has exposed its $k$-th cell and $1\le k<w$, the row immediately above must already have exposed its $(k+1)$-st cell. At $k=w$ the upper row must be complete. Thus the interior row-progress values are strictly decreasing, and repeated zeros and repeated $w$'s are allowed. Conversely these conditions on a row prefix describe an order ideal, because they impose every vertical and horizontal comparison. Occupy the sites equal to the interior progress values. An entry starts the next unstarted row, an internal move extends its unique row, and an exit completes a row. Returning to empty forces the number of moves across each of the $w$ bonds (including the entry and exit bonds) to be the same by conservation at each site. A return of length $mw$ consequently starts and completes exactly $m$ rows. The reconstruction from the empty configuration has enough rows at every earlier time. [Dal Zovo, §3, Theorem 1](https://arxiv.org/html/2605.29520v1#S3) · [Sun, fixed-width tableau recurrences](https://arxiv.org/abs/1506.07256)

Every state can be drained to the empty state, starting with the rightmost occupied site. Starting from empty, any target can be filled from right to left. The graph is strongly connected. All returns have lengths divisible by $w$ and one particle traveling through the entire system gives a return of length $w$. Its period is therefore $w$. The restriction of $T_w^w$ to the cyclic class of the empty state is primitive and has Perron root $\rho(T_w)^w$. Indeed, its classes are the diagonal blocks of $T_w^w$, and cyclic products have the same nonzero eigenvalues. The Perron left and right eigenvectors on this class are strictly positive. The Perron–Frobenius theorem now gives

```math
\lim_{m\to\infty}\frac{1}{m}\log g_{m,w}=w\log\rho(T_w).
```

## The Perron root and its curvature

With $L=w-1$ sites and unit injection and removal rates, $T_w$ is the matrix $H_0$ in the open-boundary free-fermion calculation of Nakerst, Prosen and Haque, up to transposition or the ordering of states. Their equations (35), (40) and (41) give $2w$ one-particle roots on a regular polygon of radius $2^{1/w}$. They form $w$ antipodal pairs. In a fixed auxiliary parity sector the many-body eigenvalues are half sums of signed representatives, one from each pair, subject to one occupation-parity condition. For completeness, the physical parity operator anticommutes with every new annihilator and creator because these are linear combinations of the old ones. It preserves the one-dimensional joint vacuum line and changes its sign on each creation. Consequently precisely one of the two choices of occupation parity is admitted. Its identity is immaterial in the following maximization. This also avoids dependence on the numerical parity identification in their equation (42). For $w=2$ one may check the single-site exchange matrix directly. [Nakerst, Prosen and Haque, §§II.2, IV.2–3](https://arxiv.org/html/2402.00662#S4)

For any sum, project onto its own direction. The largest possible projection chooses one vertex in the forward half-plane from each antipodal pair. In a tie the boundary pair can be chosen at either end. This selects $w$ consecutive vertices. Each such block has vector-sum magnitude $2^{1/w}/\sin(\pi/(2w))$ by the geometric sum formula. Shifting a consecutive block by one step interchanges a vertex with its antipode, hence changes exactly one sign. Both occupation parities therefore attain this upper bound. Including the half factor, we obtain

```math
\rho(T_w)=\frac{2^{1/w}}{2\sin(\pi/(2w))},\qquad
\lim_{m\to\infty}\frac{\log A^{(m)}_r}{m}=F(r+2),
\qquad F(x)=\log 2-x\log\!\left(2\sin\frac{\pi}{2x}\right).
```

For $x\ge2$ put $t=\pi/(2x)$. Differentiation gives $F'(x)=-\log(2\sin t)+t\cos(t)/\sin(t)$ and

```math
F''(x)=\frac{t^2}{x\sin^2(t)}>0.
```

For $v>0$ the increment $F(x+v)-F(x)$ is strictly increasing for $x\ge2$. In particular, given $i<j$ and $k<l$, one has

```math
F(a_i+b_k+2)+F(a_j+b_l+2)>F(a_i+b_l+2)+F(a_j+b_k+2).
```

## The determinant

For a permutation $\sigma$ write $S_\sigma=\sum_i F(a_i+b_{\sigma(i)}+2)$. Swapping the images of an inverted pair strictly increases the score by the preceding inequality. Every permutation distinct from the identity has an inversion. Hence $S_{\rm id}$ is the unique maximum. Every strip has at least one tableau. The ratio of the corresponding positive term in the determinant expansion to the diagonal term satisfies

```math
\lim_{m\to\infty}\frac1m\log\left(\frac{\prod_i H_m(i,\sigma(i))}{\prod_i H_m(i,i)}\right)=S_\sigma-S_{\rm id}<0
\qquad(\sigma\ne\mathrm{id}).
```

For $d>1$ take $q$ strictly between the largest of the finitely many $\exp(S_\sigma-S_{\rm id})$ over the nonidentity permutations and 1. Each ratio is at most $q^m$ for all sufficiently large $m$. The triangle inequality in the signed determinant expansion gives the theorem with $C=d!-1$. For $d=1$ the ratio equals one identically.

## Scope

This argument concerns the unsubdivided family across heights. The rate depends on the chosen row and column indices. Establishing positivity at a fixed height for minors of unbounded order or location, and establishing it in subdivided families, remain open here. The combinatorial correspondence and spectral calculation are prior results. Their application to Hankel minors uses the strict curvature and determinant comparison above.
