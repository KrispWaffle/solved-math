# The joint profile of pattern counts by length

Let $f_n(p)=D_{\lfloor np\rfloor}(\pi)/\binom n{\lfloor np\rfloor}$ for $0<p<1$, where $\pi$ is uniform and $D_m$ counts distinct classical patterns of length $m$. With the **same** independent Poisson variables $N_{d,e}$ of mean two for all $p$, put

```math
Y_p=\prod_{d,e\ge1}\bigl(1-p(1-p)^{d+e-1}\bigr)^{N_{d,e}} .
```

The random functions $f_n$ converge in distribution to $p\mapsto Y_p$ in $L^1(0,1)$. Their evaluations at any finite set of positive interior densities also converge jointly, including when the selected densities vary with $n$ and tend to those limits. In particular the macroscopic pattern counts at different lengths remain correlated. The source asks about the joint distribution by pattern length in addition to the aggregate count. [Source, §4](https://arxiv.org/html/2601.13194v1#S4) · [Embedding class theorem](PROOF.md) · [Displacement process](LIMIT-LAW.md) · [Uniform law on the nonempty grid](UNIFORM-PROFILE.md)

For $p,q\in(0,1)$ write $\mu_p=\exp(-2(1-p)/p)$ and $a=(1-p)(1-q)$. For lengths $m/n\to p$ and $l/n\to q$ the limiting covariance is

```math
\frac{\operatorname{Cov}(D_m,D_l)}{\binom nm\binom nl}
\longrightarrow
\mu_p\mu_q\left(\exp\left(\frac{2pqa}{(1-a)^2}\right)-1\right)>0 .
```

## Fixed-size sampling of the colors

Given the plot and a uniform $m$-subset $S$, the fixed-size class identity gives $D_m/\binom nm=\mathbb E[1/K(S)\mid\pi]$. On every compact interval $I\subset(0,1)$, the probability that $K(S)\ne2^W$ tends to zero uniformly over $m/n\in I$. Otherwise a sequence of violations would have a subsequence with $m/n\to p\in I$, contrary to the embedding class theorem.

Truncate to pairs with both distances at most $D$. A plot pair at distances $d,e$ requires at least $\max(d,e)-1$ specified intervening points to be white. Sampling without replacement, that probability is at most $(1-m/n)^{\max(d,e)-1}$ by multiplying successive conditional probabilities. If there are too few whites it is zero. The expected number of plot pairs at any two prescribed positive distances is at most two. Thus the expected number of missed local replacements is uniformly bounded by $2\sum_{\max(d,e)>D}(1-\inf I)^{\max(d,e)-1}$, which tends to zero.

For fixed $D$ the plot separation event in the distribution proof has probability tending to one. The number of retained pairs is tight by its bounded expectation. Conditional on a separated plot with at most $H$ pairs, interchangeability depends on at most $2DH$ colors. The exact probability of any specified configuration on $a+b$ labels, with $a$ specified red and $b$ specified white, is $(m)_{\underline a}(n-m)_{\underline b}/(n)_{\underline{a+b}}$. For bounded $D,H$ this differs from $(m/n)^a(1-m/n)^b$ by $o(1)$ uniformly over $m/n\in I$. There are at most $2^{2DH}$ configurations. Hence, after averaging over color choices, the truncated conditional replacement factor differs by $o(1)$ from

```math
G_{n,D}(m/n)=\prod_{d,e\le D}
\bigl(1-(m/n)(1-m/n)^{d+e-1}\bigr)^{N^{(n)}_{d,e}} .
```

Indeed independent colors of density $p$ make a pair interchangeable with probability $2p(1-p)^{d+e-1}$ and the disjoint label neighborhoods are independent. The functions are bounded by one, so taking $H\to\infty$ removes the count cutoff. The separation, truncation and localization estimates together imply

```math
\lim_{D\to\infty}\limsup_{n\to\infty}
\sup_{m/n\in I}\mathbb E\,|f_n(m/n)-G_{n,D}(m/n)|=0 .
```

## Convergence of the random functions

For fixed $D$ the finite vector of plot counts converges to $(N_{d,e})_{d,e\le D}$. Taking the product therefore gives convergence of $G_{n,D}$ as random continuous functions on $I$ in the supremum norm. The vector is integer-valued and its limit is tight, so this follows also by restricting to a finite set of count vectors. Replacing $m/n$ by $p$ on the cell $m=\lfloor np\rfloor$ changes $G_{n,D}$ by at most $C_D n^{-1}\sum_{d,e\le D}N^{(n)}_{d,e}$, since the factors are bounded by one and have bounded derivatives for fixed $D$. Its expectation is $O_D(n^{-1})$. Use a slightly larger compact interval inside $(0,1)$ for cells meeting an endpoint of $I$.

The limiting finite products converge uniformly on $I$ almost surely: the expected sum over $d,e$ of $N_{d,e}\sup_{p\in I}p(1-p)^{d+e-1}$ is finite, and all factors are positive and uniformly bounded away from zero there. This gives a continuous version of $Y_p$ throughout $(0,1)$. Testing bounded Lipschitz functions and integrating the uniform expected error over $I$ proves convergence in law in $L^1(I)$. Extending the restrictions by zero outside $I$ costs at most the length of the omitted set in $L^1(0,1)$, so exhaustion gives the asserted global convergence. For finitely many length sequences, use the same expected-error bound separately at each evaluation and the joint finite product convergence. This argument proves the evaluation statement directly.

Finally boundedness gives convergence of all the mixed moments at finitely many densities. Independence of the Poisson counts yields $\mathbb E Y_p=\mu_p$ and $\mathbb E[Y_pY_q]=\mu_p\mu_q\exp(2pq\sum_{d,e\ge1}a^{d+e-1})$. The geometric sum is $a/(1-a)^2$, establishing the covariance formula. For $p=q=1/2$ it recovers the variance constant for the aggregate count.

## Poisson approximation at macroscopic lengths

Each limiting marginal $Y_p$ is atomless. Group the displacement counts by $s=d+e$. Their sum $M_s$ has law $\mathrm{Poisson}(2(s-1))$ and is independent of all the other groups. Condition on the other factors, whose product is strictly positive almost surely. Powers of $1-p(1-p)^{s-1}\in(0,1)$ give distinct values for distinct integers $M_s$. Hence every point mass of $Y_p$ is bounded by the largest point mass of $M_s$. This bound is $O(s^{-1/2})$ by the Poisson mass formula and Stirling’s formula. Let $s\to\infty$.

For any $m/n\to p\in(0,1)$ and any proposed Poisson parameters $\lambda_n\ge0$, the total variation distance between $D_m$ and $\mathrm{Poisson}(\lambda_n)$ tends to **one**. Write $C=\binom nm\to\infty$. On a subsequence with $\lambda_n/C\to\infty$, a Poisson variable exceeds $C$ with probability tending to one by Chebyshev's inequality, while $D_m\le C$. On a subsequence with $\lambda_n/C\to c<\infty$, the normalized Poisson variable concentrates at $c$, since its variance is $\lambda_n/C^2\to0$. For each fixed $\delta>0$, its probability of $[c-\delta,c+\delta]$ tends to one. The limsup of the corresponding probability for $D_m/C$ is at most $\mathbb P(|Y_p-c|\le\delta)$ by weak convergence, and this tends to zero with $\delta$ by atomlessness. Every subsequence has a further subsequence of one of these two kinds. Projecting onto a coordinate gives the same obstruction for any vector approximation with a Poisson marginal at a macroscopic length. The source's suggestion also mentions ranges of lengths outside this regime. [Joint Poisson question](https://arxiv.org/html/2601.13194v1#S4)
