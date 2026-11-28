# The expected number of distinct classical patterns

Let $D_m(\pi)$ be the number of distinct patterns among the $m$-subsets of positions. Whenever $m/n\to p\in(0,1)$,

```math
\frac{\mathbb E D_m(\pi)}{\binom nm}\longrightarrow
\exp\left(-\frac{2(1-p)}p\right).
```

In particular, for the total number $X_n=\sum_m D_m(\pi)$ one has $\mathbb E X_n/2^n\to e^{-2}$. This answers the exact-mean question in §4 of the source. [Original question](https://arxiv.org/html/2601.13194v1#S4) · [Withdrawal of an earlier bound](https://arxiv.org/abs/2601.13194)

## Two orders and an embedding class

Give $n$ labels two independent uniform linear orders, called horizontal and vertical. Reading vertical ranks in horizontal order gives a uniform permutation. Fix a set $S$ of $m$ red labels and call the other labels white. Write $K(S)$ for the number of $m$-sets $T$ inducing the same permutation as $S$. In either order there is only one increasing bijection $S\to T$, so $T$ is counted exactly when the horizontal bijection also preserves the vertical order. Averaging reciprocals of class sizes counts each distinct pattern once:

```math
\mathbb E D_m/\binom nm=\mathbb E[1/K(S)].
```

Label symmetry permits keeping $S$ fixed. Call a red-white pair individually interchangeable when the map sending that red to the white and **fixing each other red** preserves both orders. Equivalently, no other red label lies between the two in either order. Let $W$ count these pairs. We prove that $K(S)=2^W$ with probability tending to one and $W$ converges to $\mathrm{Poisson}(4(1-p)/p)$.

Fokuoh’s 2018 thesis already counted same-rank single exchanges by the horizontal and vertical gaps and their intersection (Theorem 4.1, Type A repeats). The issue for the mean is that several exchanges can coexist and other bijections can move common labels. The following support estimate handles those alternatives. [Fokuoh’s thesis](https://dc.etsu.edu/etd/3461/)

## Counting nonlocal bijections

For a candidate bijection $\phi:S\to T$, put $b=|S\setminus T|$ and let $l$ be the number of red labels moved by $\phi$. An increasing bijection cannot have a nontrivial directed cycle: an increase or decrease at any edge would persist around the cycle. Removing the $f=m-l$ fixed points therefore leaves $b$ directed paths with $l$ edges and $l+b$ vertices altogether. Each starts at a red label outside $T$ and ends at a white label. Apart from the identity, $1\le b\le l$.

For a fixed map with path lengths $l_1,\ldots,l_b$, let $q=\sum_j\lceil l_j/2\rceil$. Alternate edges of each path give $q$ vertex-disjoint directed edges. A necessary condition in one uniform order is that the tails and heads of these edges appear in matching relative orders. The two lists are independent uniform permutations, so this costs a factor $1/q!$. In particular $q\ge b$ and $q\ge l/2$.

Condition on the relative order of the $l+b$ moving vertices. A fixed point can be inserted only at a cut which no edge crosses, since it must compare the same way with both endpoints of each edge. Such a cut separates entire nonempty paths. Including the two exterior cuts, there are at most $b+1$ permissible slots. The fixed vertices, in their own order, are uniformly interleaved with the moving vertices. Thus the one-order probability of the map is at most

```math
\frac{1}{q!}\frac{\binom{f+b}{b}}{\binom{f+l+b}{l+b}}.
```

The choices of moved red labels, path starts, white ends, their matching, the ordered internal vertices and the positive path lengths give exactly

```math
\binom ml\binom lb\binom{n-m}b\,b!(l-b)!\binom{l-1}{b-1}
=(m)_{\underline l}\binom{n-m}b\binom{l-1}{b-1}
```

maps. Order the starts by their label to specify which path gets each length. For two independent orders square the one-order probability. For $l\le 8n/\log n$ and large $n$, $f\ge c n$ with $c>0$ depending on $p$. The binomial ratio is $(l+b)!(f+b)!/(b!(f+l+b)!)\le(2l)^l/f^l$. Writing $E_{l,b}$ for the expected number of preserving maps of these sizes, we obtain

```math
E_{l,b}\le C^l n^{b-l}l^{2l-b-2q_0},
\qquad q_0=\max(b,\lceil l/2\rceil).
```

Indeed $\binom{l-1}{b-1}\le2^l$, and $b!\ge l^b e^{-C l}$ follows from $b!\ge(b/e)^b$ and $b\log(l/b)\le l/e$. The same bound applies to $q_0!$. For $b\le l/2$ this is at most $C^l(l/n)^{l-b}$. For $b\ge l/2$ it is at most $C^l(l/n)^{l-b}l^{-(2b-l)}$. In either range, for $M\le l\le8n/\log n$, set $\delta=\max(8/\log n,1/M)$. The bound is at most $(C\sqrt\delta)^l$, since the exponents of the two small factors sum to at least $l/2$. Summing over $b,l$ shows the probability of such a map tends to zero as first $n\to\infty$ and then $M\to\infty$.

For $l>8n/\log n$, expose the horizontal order first. Each choice of $T$ now determines at most one map. Its vertical probability is at most $1/\lceil l/2\rceil!$ from the disjoint edges. There are at most $2^n$ choices of $T$. Stirling's bound makes their total contribution $o(1)$. In particular the maximum support of any preserving map is tight.

It remains to consider bounded $l$. If $b<l$, the estimate $E_{l,b}=O(n^{b-l})$ rules out every such map with probability tending to one. If $b=l$, all paths have one edge. In each order the endpoints of a pair lie in the same gap of the untouched red labels. The event that two of the pairs occupy the same such gap in either order costs an extra $O(1/n)$. In detail, in that order the $2b$ specified vertices occupy at most $b-1$ gaps of $f$ fixed vertices. For fixed $b$ this has probability $O(f^{b-1}/\binom{f+2b}{2b})=O(f^{-b-1})$, by choosing the nonempty gaps and the block lengths. The other order costs $O(f^{-b})$. There are $O(n^{2b})$ candidate maps. With probability tending to one, all preserving maps thus consist of single replacements in distinct gaps in each order. In particular each replacement is individually interchangeable.

## Poisson replacements and the converse

For fixed $h$, expand $\mathbb E (W)_{\underline h}$ over ordered lists of distinct red-white pairs. Group the labels into connected components of the graph of these pairs. With $v$ vertices and $c$ components, all vertices of each component must lie in one gap of the untouched reds in each order. For specified labels the probability is $O(m^{-(v-c)})$ in one order, by choosing at most $c$ occupied gaps out of $m-O(1)$ and dividing by the number of insertions of $v$ vertices. With $O(n^v)$ ways to choose labels, the two-order contribution is $O(n^{2c-v})$. For fixed $h$ this tends to zero whenever a component contains at least three vertices. It also proves that with high probability no two interchangeable pairs share a vertex, by taking $h=2$.

For disjoint pairs the single-order probability is asymptotic to $2^h/m^h$. Indeed the configurations in which each of the $h$ named pairs forms a block in the order of all red labels and the $h$ named whites have probability $2^h m!/(m+h)!$. In any other permissible configuration, at least two pairs occupy the same gap of the $m-h$ untouched reds, which costs $O(m^{-h-1})$ by the preceding gap count. Squaring and multiplying by $(m)_{\underline h}(n-m)_{\underline h}$ gives the factorial moments $(4(1-p)/p)^h$. The Poisson distribution is determined by its moments, proving the asserted convergence.

Taking $h=2$ in the shared-gap estimate also rules out, with probability tending to one, two individually interchangeable disjoint pairs in a common gap of the reds outside those two pairs, in either order. Thus the intervals between interchangeable partners are disjoint in each order. Replacing any chosen subset of partners preserves both orders at once: no interval crosses an untouched red or another interval. Different subsets give different images. Together with the exclusion of all other maps, this proves $K(S)=2^W$ with probability tending to one.

The reciprocal class size is bounded by one. Hence its expectation converges to the Poisson generating function at $1/2$, namely $\exp(-2(1-p)/p)$. To sum over lengths, let $m$ be binomial with parameters $n,1/2$. Its ratio to $n$ tends to $1/2$ in probability. The fixed-length assertion applies along every sequence $m/n\to1/2$, so the mixture of the bounded expectations tends to $e^{-2}$.

For the binomial moments in the Lean implication the same mixture applies. At every fixed $h$ the counting bounds above are uniform when $m/n$ stays in $[1/3,2/3]$, and the disjoint-pair term tends to $4^h$ along every sequence $m/n\to1/2$. Outside that interval the binomial length has exponentially small probability, while $W^h\le n^{2h}$. Thus $\mathbb E\binom Wh\to4^h/h!$. The probability of a class-size mismatch tends to zero by the bounded indicator and the same length concentration. [Exact formal implication](../../lean/SolvedMath/RandomPatternMoments.lean)
