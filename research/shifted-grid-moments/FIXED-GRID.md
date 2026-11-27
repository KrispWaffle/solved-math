# Fixed grids, entropy, and dilated Hankel minors

Fix the entire shifted grid of Conjecture 10.5, including its height $m\ge2$, horizontal subdivision counts $h_1,\ldots,h_m$ and vertical subdivision counts $v_1,\ldots,v_{m-1}$. Set $\alpha_i=h_i+1$, $D=\sum_i\alpha_i$, $V=\sum_i v_i$, $d=D+V$. Write $N(j)$ for the number of permutations with the $j$ prescribed occurrences and $A_r=N(r+1)$. Previous work shows $\log N(j)=Vj\log j+O(j)$ and determines the exponential rate when $V=0$. [Source grid and permutations, §7.1](https://arxiv.org/html/2611.12829v1#S7) · [Earlier growth bounds](https://github.com/the-omega-institute/trureturing/issues/29090)

**Theorem 1.** There is a finite constant $c$ such that

```math
\log N(j)=Vj\log j+cj+o(j).
```

The formula below determines $c$ by a variational problem on $m$ probability distributions on the unit interval.

**Theorem 2.** Suppose $V>0$. Fix strictly increasing lists $a_1,\ldots,a_k$ and $b_1,\ldots,b_k$ of nonnegative integers. For every sufficiently large integer $s$, the matrix $H_s=(A_{s(a_i+b_l)})_{i,l=1}^k$ has positive determinant. Its determinant divided by the product of its diagonal entries tends to one exponentially in $s$. The grid and both lists stay fixed. This conclusion applies to every grid with a vertical subdivision, at its actual height.

## Integrating out the vertical chains

A packing is a linear extension of the source grid. Assign each cell a coordinate between zero and one. The volume of the region where coordinates respect all comparisons is $N(j)/n!$ for $n=m+jd$, by partition into the equally sized simplices indexed by permutations. Horizontal row $i$ is a chain of $n_i=j\alpha_i+1$ cells. Its checkpoints $u_{i,q}$ have ranks $1+q\alpha_i$ for $0\le q\le j$. Sample $n_i$ independent uniform random variables and write their ordered values as $X_{i,1},\ldots,X_{i,n_i}$. Sample rows independently. In cell interval $q=0,\ldots,j-1$ the vertical chain from row $i$ to row $i+1$ has available length

```math
G_{i,q}=X_{i+1,1+q\alpha_{i+1}}-X_{i,1+(q+1)\alpha_i}.
```

All these lengths must be positive, including when $v_i=0$. At positive length the volume of the $v_i$ ordered interior coordinates is $G_{i,q}^{v_i}/v_i!$. These interior coordinates are disjoint and all their comparisons follow from the displayed edges. Consequently

```math
N(j)=\frac{n!}{\prod_i n_i!\;\prod_{i<m}(v_i!)^j}\;
\mathbb E\left[\mathbf1_{\{G_{i,q}>0\ \forall i,q\}}\prod_{i,q:v_i>0}G_{i,q}^{v_i}\right].
```

## The variational constant

Let $\lambda$ denote uniform probability measure on $[0,1]$. For a tuple of laws $\mu_i$, let $Q_i$ be their increasing quantiles and $I=\sum_i\alpha_i D(\mu_i\Vert\lambda)$, using natural logarithms and probability relative entropy. Restrict to tuples with $Q_i(u)\le Q_{i+1}(u)$ almost everywhere. Define

```math
S=\sup_{\mu}\left\{
\sum_{i:v_i>0}v_i\int_0^1\log(Q_{i+1}(u)-Q_i(u))\,du-I
\right\}.
```

Use $\log 0=-\infty$ in the potential. Tuples of infinite entropy have value $-\infty$. The supremum is at most zero and is finite below by choosing uniform laws on strictly separated intervals of positive length. Then

```math
c=d\log d-\sum_i\alpha_i\log\alpha_i-V-\sum_{i<m}\log(v_i!)+S.
```

We prove that the logarithm of the expectation divided by $j$ tends to $S$. Stirling's formula applied to the preceding prefactor gives the displayed constant, including the $-V$ term. For $V=0$, equal uniform laws give $S=0$, recovering the earlier endpoint.

### Upper bound

The vector of empirical row laws is a random element of the compact product $\mathcal P([0,1])^m$ with its weak topology. Sanov's theorem and independence give the large-deviation upper bound with speed $j$ and rate $I$. Indeed each row has speed $n_i$ with $n_i/j\to\alpha_i$. Multiplying the bounds on closed product neighborhoods and using a finite cover of a closed set gives the asserted product upper bound. [Sanov's empirical-measure theorem and Laplace formulation](https://arxiv.org/abs/1609.04744)

Write $\Phi_j$ for $j^{-1}$ times the logarithm of the integrand, with value $-\infty$ on forbidden configurations. Let $\Phi$ denote the potential in $S$, with value $-\infty$ when the quantiles fail the required order. For any converging sequence of empirical tuples $\mu^{(j)}\to\mu$, one has $\limsup_j\Phi_j\le\Phi(\mu)$. To see this, identify each interval $[q/j,(q+1)/j)$ with its pair of order-statistic indices in $G_{i,q}$. Their quantile arguments are $[1+q\alpha_{i+1}]/n_{i+1}$ and $[1+(q+1)\alpha_i]/n_i$, both within $O(1/j)$ of the interval. At every common continuity point of the limiting quantiles in $(0,1)$, these order statistics converge to the corresponding quantiles. This follows by bounding them between quantiles at neighboring continuity levels and shrinking the neighborhood. Monotonicity leaves at most countably many excluded levels per row. Along any subsequence of allowed tuples the limiting gaps must be nonnegative almost everywhere. Applying Fatou's lemma to the nonnegative functions $-v_i\log G_{i,q}$ on the step intervals gives the asserted bound, including vanishing limiting gaps.

For detail on the Laplace upper bound, fix $M>0$. Around each tuple choose a closed neighborhood small enough that $I$ has infimum at least $\min(I(\mu),M)-\varepsilon$. The sequential bound on $\Phi_j$ also permits a neighborhood where $\Phi_j\le\max(\Phi(\mu),-M)+\varepsilon$ for every sufficiently large $j$. Otherwise a shrinking sequence of neighborhoods gives a contradicting convergent sequence. The interiors of joint choices cover the compact space, so retain finitely many. Applying the probability upper bound on each closed neighborhood shows that the limiting exponent is at most $\max(S,-M)+2\varepsilon$: if either truncation is active, nonpositivity of $\Phi$ and nonnegativity of $I$ bound the truncated difference by $-M$. Let $M$ increase and $\varepsilon$ decrease to zero.

### Lower bound

Take any ordered tuple with finite entropy and finite potential. Mix each law with the same $\eta$ proportion of uniform measure. The resulting laws remain stochastically ordered, have densities at least $\eta$, and their entropy costs are at most $(1-\eta)I$ by convexity. Their continuous strictly increasing distribution functions have $1/\eta$-Lipschitz quantiles. Next send row $i$ through the affine map $x\mapsto(1-\delta)x+\delta i/(m+1)$ for $0<\delta<1$. The new tuple $\nu$ has adjacent quantile gaps at least $\delta/(m+1)$ everywhere. Its rows have interval supports and densities bounded below there. Shrinking by the factor $1-\delta$ adds exactly $-D\log(1-\delta)$ to the weighted entropy.

Sample the rows from $\nu_i$. Under this product law their empirical quantiles converge uniformly to the new quantiles, including endpoints because all samples belong to the support intervals and the population quantiles are Lipschitz. For example, transform each sample through its continuous distribution function, apply the uniform empirical distribution theorem to the uniform samples, and then use the Lipschitz quantile map. The sampling indices differ from the integration parameter by $O(1/j)$ as above. With probability tending to one every discrete gap is positive and $\Phi_j$ approaches $\Phi(\nu)$. The law of large numbers applied to the row log densities also gives the log likelihood ratio of the tilted product law relative to the original product law, divided by $j$, converging to $I(\nu)$. Integrability follows from finite entropy and the bound on the negative part of $x\log x$ on $[0,1]$. Restricting the expectation to the intersection of these two high-probability events gives a limiting lower bound of $\Phi(\nu)-I(\nu)$.

For fixed $\delta$, let $\eta$ decrease to zero. Quantiles converge almost everywhere to the original quantiles before the affine maps. The separated gaps bound the logarithms uniformly, permitting dominated convergence after those maps. Each new limiting gap is at least $1-\delta$ times its original size, so the potential is at least $\Phi(\mu)+V\log(1-\delta)$. Together with the entropy bound this loses at most $-(V+D)\log(1-\delta)$ relative to $\Phi(\mu)-I(\mu)$. Let $\delta$ decrease to zero and then take the supremum. This proves Theorem 1.

## Dilation of a Hankel minor

Replacing $j$ by $r+1$ gives $\log A_r=Vr\log r+cr+o(r)$. For each fixed nonnegative integer $z$ this implies

```math
\frac{\log A_{sz}}s-Vz\log s-cz\longrightarrow Vz\log z
\qquad(s\to\infty),
```

with $0\log0=0$, since $A_0=1$. Across the permutation terms in the determinant, the sum of $a_i+b_{\sigma(i)}$ is constant. The terms involving $\log s$ and $c$ cancel when comparing to the diagonal. The remaining score is $V\sum_i(a_i+b_{\sigma(i)})\log(a_i+b_{\sigma(i)})$. Strict convexity of $x\log x$ on $[0,\infty)$ gives a strict increase on removing any inversion when $V>0$, including a zero sum at the lower left endpoint of an increasing pair of lists. The identity is therefore the unique maximum. Each off-diagonal permutation product divided by the diagonal product decays exponentially. Summing the finitely many signed terms proves Theorem 2.

At any given scale a minor can still fail the conjecture. The estimate holds for dilations of a fixed pair of index sets. It leaves positivity for adjacent high-order moments, arbitrary undilated minors and a representing measure unresolved.
