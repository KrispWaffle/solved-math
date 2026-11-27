# A limit shape for the spine of a random cluster-poset extension

Fix $1\le a<b\le m$. Write $p=a-1$, $q=m-b$, $c=b-a$, $N=cn$, and $D=(m-1)n+1$. Use one-based ranks in a uniform linear extension $L$ of the poset in Definition 1.3 of Lee and Sah. Set

```math
 h(t)=t^{p/c}(1-t)^{q/c},\qquad B=\int_0^1 h(t)\,dt,\qquad G(x)=B^{-1}\int_0^x h(t)\,dt,\qquad f=G^{-1}.
```

**Theorem.** For every fixed $\varepsilon>0$ there are positive constants $C,\kappa$ depending only on $m,a,b,\varepsilon$ such that, for $n\ge1$,

```math
 \Pr\left(\max_{0\le i\le n}\left|\frac{\operatorname{rank}_L(X_i)}{D}-f\left(\frac{i+1}{n+2}\right)\right|>\varepsilon\right)\le C e^{-\kappa n}.
```

This yields Conjecture 6.1, including a deterministic error tending to zero with probability tending to one by a diagonal choice of tolerances. Figure 3 of the source plots the fraction of the other elements that precede the marked point. For one-based rank $r$, the difference between $r/D$ and $(r-1)/(D-1)$ equals $(D-r)/(D(D-1))\le1/D$ when $D>1$. Both normalizations give the stated limit. [Lee–Sah, §6.2](https://arxiv.org/pdf/1807.04921)

## The law of all spine coordinates

Give each of the $D$ elements an independent uniform label in $(0,1)$ and condition on the labels increasing along every chain. The strict order of all labels is a uniform permutation independent of their sorted values. The conditioning selects exactly the linear extensions. Thus the induced extension is uniform, and the sorted list of all $D$ labels still has the ordinary uniform order-statistic law. [Lee–Sah, §3](https://arxiv.org/pdf/1807.04921)

Keep every label on the common spine, including its $c-1$ unmarked elements between each pair of marked points. In increasing order write these coordinates as $0<z_0<\cdots<z_N<1$. The coordinate of $X_i$ is $z_{ci}$. For window $i+1$, its $p$ lower labels form a chain below $z_{ci}$, and its $q$ upper labels form a chain above $z_{c(i+1)}$. These labels are disjoint among windows. Given the spine, satisfying these chain constraints is sufficient to satisfy every relation generating the poset. Integration over the lower and upper chains supplies the factors $z_{ci}^p/p!$ and $(1-z_{c(i+1)})^q/q!$. Hence the ordered spine has density proportional to

```math
 W(z)=\prod_{i=0}^{n-1}z_{ci}^p(1-z_{c(i+1)})^q.
```

## Comparison with independent beta samples

Use a reference probability law $Q$. Draw $N$ independent observations with density $h/B$, put them in increasing order as $z_1,\ldots,z_N$, and draw $z_0$ independently and uniformly on $(0,1)$. The spine law is obtained from $Q$ by weighting with

```math
 R(z)=\mathbf 1_{\{z_0<z_1\}}\frac{W(z)}{H(z)},\qquad H(z)=\prod_{s=1}^N h(z_s),
```

then dividing by $\mathbb E_Q R$. The constants $N!/B^N$ and the chain factorials do not depend on $z$. Ties and boundary values have probability zero.

On $z_0<z_1$, the $c$ points $z_{ci+1},\ldots,z_{c(i+1)}$ lie in $[u,v]=[z_{ci},z_{c(i+1)}]$. The product of their $h$ values is between $u^p(1-v)^q$ and $v^p(1-u)^q$. Dividing and multiplying over the windows telescopes both endpoint ratios. It gives

```math
  \left(\frac{z_0}{z_N}\right)^p\left(\frac{1-z_N}{1-z_0}\right)^q\le R(z)\le 1.
```

This control also gives a polynomial lower bound for the normalizer. The beta density is bounded by $M=1/B$. Put $\delta=1/(8(1+M)N)$. By a union bound, all $N$ beta samples belong to $[2\delta,1-2\delta]$ with probability at least $1-4NM\delta\ge1/2$. Independently, $z_0$ lies in $[\delta,2\delta]$ with probability $\delta$. On their intersection the two ratios in the lower bound are each at least $\delta$. Consequently

```math
 \mathbb E_Q R\ge\tfrac12\delta^{p+q+1},\qquad
 \Pr_{\rm spine}(E)\le 2[8(1+M)N]^{p+q+1}Q(E)
```

for every measurable spine event $E$. For $p=0$ or $q=0$ the corresponding power equals one. This includes $p=q=0$.

## Uniform concentration and the transfer to discrete ranks

Under $Q$ the variables $G(z_s)$, $1\le s\le N$, are the sorted values of $N$ independent uniform observations. For any $\eta>0$ the Dvoretzky–Kiefer–Wolfowitz inequality bounds the probability that any of them differs from $s/N$ by more than $\eta$ by $2e^{-2N\eta^2}$. Indeed the empirical distribution at each observation is $s/N$. The previous density bound transfers this estimate to the spine with the displayed polynomial factor. [Massart’s inequality](https://doi.org/10.1214/aop/1176990746)

Lean also checks an elementary bound of $2Ne^{-2N\eta^2}$ for this uniform-sample event. For each rank $s$, count the observations below the two fixed thresholds $s/N-\eta$ and $s/N+\eta$. A deviation at rank $s$ forces one of those binomial counts to deviate by at least $N\eta$. Hoeffding’s inequality at each threshold and a union bound over $s$ give the extra factor $N$, which the final exponential estimate absorbs. [Lean proof](../../lean/SolvedMath/ClusterOrderStatistics.lean)

On the complementary event, $|G(z_{ci})-i/n|\le\eta$ for $1\le i\le n$. The ordering of the actual spine also gives $0\le G(z_0)\le G(z_1)\le\eta+1/N$. For all $i$, $|i/n-(i+1)/(n+2)|\le1/(n+2)$. The inverse $f$ is uniformly continuous on $[0,1]$ because $G$ is a continuous strictly increasing bijection there. Choose $\eta>0$ small enough, then $n$ large enough, that an argument difference of $\eta+1/N+1/(n+2)$ changes $f$ by at most $\varepsilon/2$. Except on the stated exponentially unlikely event, all marked labels thus lie within $\varepsilon/2$ of the claimed quantiles.

Let $v_1<\cdots<v_D$ be the ordered values of **all** labels under the conditioning. By the first step their distribution is still that of sorted independent uniform observations. Another application of the same inequality, with tolerance $\varepsilon/2$, gives $|v_j-j/D|\le\varepsilon/2$ for every $j$, except with probability at most $2e^{-D\varepsilon^2/2}$. Since $z_{ci}=v_{\operatorname{rank}_L(X_i)}$, the triangle inequality gives the asserted rank estimate simultaneously, including $X_0$ and $X_n$. The union bound does not require independence of the two good events. As $N=cn$ and $D\ge n$, a fixed polynomial in $n$ multiplying an exponential decay is bounded by $Ce^{-\kappa n}$ after decreasing $\kappa$. Increasing $C$ covers the finitely many small $n$.

The complete Lean proof uses the elementary order-statistic estimate above. It takes the boundary margin $B/(8N)$ and proves the tail inequality with positive constants at every stack size. A separate corollary verifies the same limit in the coordinate convention of Figure 3. [Formal proof](../../lean/SolvedMath/ClusterLimit.lean) · [Figure 3](../../lean/SolvedMath/ClusterFigure.lean)
