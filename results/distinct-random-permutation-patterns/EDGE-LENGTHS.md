# Sparse patterns and nearly full patterns

Write $D_m$ for the number of distinct length-$m$ patterns. For every sequence of **nonempty** lengths with $m/n\to0$, the fraction $D_m/\binom nm$ tends to zero in $L^1$. At the other edge write $k=n-m$ and assume $1\le k=o(n)$. Let $H_n$ be the number of bonds, pairs in adjacent positions with consecutive values. Then

```math
\mathbb E\left|\frac nk
\left(1-\frac{D_{n-k}}{\binom nk}\right)-H_n\right|\longrightarrow0 .
```

In particular the scaled loss converges in law to $\mathrm{Poisson}(2)$, and every finite collection of such length sequences has the **same** Poisson variable in its joint limit. For $k=1$, Homberger already identified the exact deficit with the bond count. The estimate below covers arbitrary sublinear deletion counts, including $k\to\infty$. At $k=0$ the normalized pattern count is one. [Single-deletion formula](https://arxiv.org/abs/1211.7117) · [Bond limit](https://arxiv.org/abs/1706.01557) · [Macroscopic profile](LENGTH-PROFILE.md)

## Vanishing sampling density

Use $S,K,W$ from the embedding class proof, with $m$ red labels and $u=n-m$ white. Distinct individually allowable red-white pairs give distinct single-exchange images, so $K\ge1+W$ always. For bounded positive $m$, the bound $D_m\le m!$ gives the conclusion. Suppose $m\to\infty$ and $m/n\to0$. The probability a specified white is next to a particular red in the order restricted to the reds and that white equals $2/(m+1)$. Independence of the two orders gives

```math
\mathbb E W=\frac{4mu}{(m+1)^2}\longrightarrow\infty .
```

For two ordered distinct red-white pairs, the exact one-order probabilities according to their endpoints are
```math
P_{\rm disjoint}=\frac{4m+2}{m(m+1)(m+2)},\qquad
P_{\rm same\ red}=\frac6{(m+1)(m+2)},\qquad
P_{\rm same\ white}=\frac2{m(m+1)} .
```

For disjoint pairs, in the order of the $m$ reds and two specified whites the two partners can form disjoint adjacent blocks in $4m!$ orders. The only additional orders have the two whites between their respective reds in reversed partner order, giving $2(m-1)!$ orders. If the red is shared, the three named labels must form one block in any of six orders. If the white is shared, it must sit between the two named reds in one block, in either orientation. Thus the shared-red count is $6m!$ out of $(m+2)!$ and the shared-white count is $2(m-1)!$ out of $(m+1)!$. Square each probability for the two independent orders. The disjoint contribution to $\mathbb E(W)_{\underline2}$ is asymptotic to $(\mathbb E W)^2$. The shared-red and shared-white contributions are $O(mu^2m^{-4}+m^2um^{-4})=o((\mathbb EW)^2)$. Hence $W/\mathbb EW\to1$ in probability. Boundedness of $1/K\le1/(1+W)$ now gives $\mathbb E D_m/\binom nm\to0$. These two cases cover every length sequence by subsequences. [Gap and block counts](PROOF.md)

## An error bound at the high-density edge

Set $\delta=k/n$ and assume $1\le k\le n/2$. In a plot with a uniform $m$-subset of reds, let $W_1$ count the bonds with one endpoint of each color. Its conditional mean is $2mkH_n/[n(n-1)]$. Also $\mathbb E H_n=2(n-1)/n$ by direct pair counting. Since $W_1\le W$, the formula above yields

```math
\mathbb E(W-W_1)
=4mk\big((m+1)^{-2}-n^{-2}\big)=O(\delta^2).
```

We also have $\mathbb E(W_1)_{\underline2}=O(\delta^2)$. There are $O(1)$ expected ordered pairs of disjoint bonds by the bounded-displacement counting argument. Their activity requires two different whites, costing at most $4k(k-1)/(n(n-1))$. Bonds sharing an endpoint have expected number $O(1/n)$: three points in a connected configuration of bounded displacement give $O(n)$ assignments on each axis with probability $1/(n)_{\underline3}$. Activity in that case requires a white among the three points, costing at most $3\delta$. Since $\delta\ge1/n$, both contributions are $O(\delta^2)$.

Let $E$ denote the existence of a preserving nonidentity map that has at least two paths or a path of length at least two, in the notation $b,l$ of the mean proof. We claim $\mathbb P(E)=O(\delta^2)$. In the range $l\le8n/\log n$, retain the factor $\delta^b$ in the estimate for $E_{l,b}$, from $\binom{k}{b}\le(\delta n)^b/b!$. All other constants in that estimate can be chosen uniformly for $m\ge n/2$. For $b\ge2$ factor out $\delta^2$. The sum of the old bounds is bounded uniformly in $n$: for fixed $l$ it is bounded, and summing over $M\le l\le8n/\log n$ is dominated by a convergent geometric tail for a fixed sufficiently large $M$ and all sufficiently large $n$. For $b=1$, $l\ge2$, use

```math
E_{l,1}\le C^l\delta(l/n)^{l-1}
\le \frac{\delta}{n}C^l l(8/\log n)^{l-2}.
```

Summing costs $O(\delta/n)=O(\delta^2)$. Above the support cutoff, the bound $2^n/\lceil4n/\log n\rceil!$ is exponentially small. This proves the claim. [Uniform support bound](PROOF.md)

When $W_1\le1$, $W=W_1$ and $E$ fails, the class has exactly $1+W_1$ images. Thus $1-1/K=W_1/2$ there. When $W_1\ge2$, the error is bounded by $W_1(W_1-1)$; when $W_1\le1$ it is at most one. This proves

```math
\mathbb E\left|\left(1-\frac1K\right)-W_1/2\right|=O(\delta^2).
```

Conditioning on the plot and applying the triangle inequality now gives

```math
\mathbb E\left|\left(1-\frac{D_m}{\binom nm}\right)
-\frac{mk}{n(n-1)}H_n\right|=O(\delta^2).
```

Multiplication by $n/k$ gives an $O(\delta)$ error. Replacing $mH_n/(n-1)$ by $H_n$ costs at most $O(\delta)$ in $L^1$. This proves the scaled limit. Applying it to finitely many lengths in the same plot gives the joint assertion.

## Endpoints of the limiting profile

The continuous limiting function on $(0,1)$ extends almost surely to $Y_0=0$ and $Y_1=1$. As $p\uparrow1$ this follows by summable domination of the logarithms. As $p\downarrow0$, put $r=\lfloor1/p\rfloor$. For $d,e\le r$ and $p\le1/2$, $(1-p)^{d+e-1}\ge1/16$ since $(1-p)^{1/p}\ge1/4$. Hence $-\log Y_p\ge(p/16)\sum_{d,e\le r}N_{d,e}$. In an enumeration by successive square shells the strong law gives $\sum_{d,e\le r}N_{d,e}\sim2r^2$ almost surely. This proves the limit. The bond count is exactly the displacement coordinate $N^{(n)}_{1,1}$ in the interior profile proof. Retaining that coordinate in its finite approximations gives joint convergence of the scaled high-density deficits and the interior profile; their common endpoint variable is $N_{1,1}$. For each interior $p$, the covariance of $N_{1,1}$ with $Y_p$ is $-2p(1-p)\mu_p$, by the Poisson generating function. This is also the limit of the covariances of the scaled deficits and the normalized interior counts. Indeed those counts are bounded, the deficit approximation holds in $L^1$, and the bond counts have bounded second moments by the disjoint and shared-endpoint counts above. The single empty subset at length zero contributes one empty pattern.
