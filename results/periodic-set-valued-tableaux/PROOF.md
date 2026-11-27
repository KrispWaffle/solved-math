# A finite transfer for every diagram and excess

We work in the Sun–Chan orientation of the shifted band. The [coordinate audit](COORDINATES.md) gives the conclusion for the different translation and order printed together in Dal Zovo v1. The generalized word predicate throughout is its equation (4). [Sun](https://arxiv.org/abs/1506.07256) · [Chan](https://arxiv.org/abs/1803.05594) · [Dal Zovo, §§2.2–3.1](https://arxiv.org/html/2605.29520v1#S2)

## Cells and profiles

For an integer $w\ge1$ the band contains the cells $(k,k+i)$ for $k\in\mathbb Z$, $0\le i<w$, in the coordinatewise order. A profile $p=(p_0,\ldots,p_{w-1})$ has integer entries and $p_i-p_{i+1}\in\{0,1\}$. It specifies the ideal of all cells with $k\le p_i$ on diagonal $i$. For $w\ge2$ the elementary predecessors of a cell are $(k,k+i-1)$ or $(k-1,k+i)$ when their diagonals are present. For $w=1$ the single diagonal is a chain with predecessor $(k-1,k-1)$. In general the largest permissible height cannot increase to the right and can decrease by at most one per diagonal. For two profiles $p\le q$, write $D(p,q)$ for the finite difference of these ideals. A one-period difference $D(p,p+1)$ has one cell per diagonal; its consecutive cells are one rightward or upward lattice step apart. Every such zigzag arises this way. Replacing $1$ by $k$ takes the union of $k$ consecutive translates of this zigzag. For $w\ge2$ constant profiles give the ordinary shifted strips in Sun’s range. Width one here is the product-order extension. A convention using only comparisons within common rows or columns gives a different poset for singleton rows.

Every ideal of $D(p,q)$ has an intermediate profile $h$, $p\le h\le q$. Its union with the lower infinite ideal is again an ideal. The intersection on each diagonal is an initial segment. Downward closure at neighboring diagonals gives exactly the two bounds on the adjacent differences. Conversely an intermediate profile gives such an ideal. This also handles width one, equal outlines and the empty difference.

An outline $x$ records just the $w-1$ bits $x_i=h_{i-1}-h_i$ for $1\le i<w$. Increasing $h_i$ by one is legal precisely when the existing left bit is 1 and the existing right bit is 0, omitting a condition at a missing neighbor. This enters a particle on the left, moves it across an internal bond, or removes it on the right. Call this a discovery at bond $i$. A decrement is legal precisely under the reversed bit conditions. This is the direct profile version of Dal Zovo's ordinary tableau–walk correspondence. Given an initial profile, the terminal outline together with the number of discoveries determines the terminal profile uniquely: equal outlines differ by a constant integer vector and their sizes then differ by a multiple of $w$.

## Repetitions at an actual cell

In a surjective word satisfying equation (4), the cells seen so far form an ideal. An unseen strict predecessor of an already seen cell could never appear later. First appearances therefore form an ordinary linear extension. At any stage one may repeat exactly the maximal cells of the seen ideal: a later repeat of a nonmaximal cell would put it after one of its strict successors. Conversely, taking legal first appearances and such repetitions gives a word obeying every pairwise comparison. Terminating at the whole diagram gives surjectivity.

On diagonal $i$ there is at most one repeatable cell, the top seen cell $(h_i,h_i+i)$. It exists in the difference precisely when $h_i>p_i$. It is maximal precisely when $h-e_i$ is a profile. Removing it then leaves an ideal. Thus a finite state consists of the outline $x$ and the set $U$ of bonds at which a discovery has occurred. At a legal forward move at $i$ change the outline and insert $i$ into $U$. At a repeat one may choose any reverse-legal bond $i\in U$, leaving both components fixed. In particular the initial state $(x,\varnothing)$ has no legal repeats even if the initial outline has removable corners. At width one the single bond always allows a discovery and becomes repeatable after its first discovery.

Let $A$ count discovery transitions on these finite states, and let $B$ be diagonal with $B_{(x,U),(x,U)}$ the number of eligible repeats. The matrices use row-to-column orientation; multiple choices contribute their multiplicity. There are at most $2^{w-1}2^w$ states. Let $e$ select the initial state, and let $v_y$ indicate all states with terminal outline $y$. Write $s=|D(p,q)|$ and $y$ for the outline of $q$. For every $b\ge0$,

```math
f^{D(p,q)}(s+b)=[z^s u^b]\ e^\mathsf T(I-zA-uB)^{-1}v_y .
```

To prove this, expand the inverse as a geometric series. A path yields its physical word by recording the cell just raised at a discovery and the current top cell of the chosen bond at a repeat. Its final profile must be $q$ by the outline and size condition. The intermediate profiles are coordinatewise increasing, so they never overshoot $q$. Conversely, the first-appearance record of an admissible word reconstructs these operations uniquely, including the chosen physical cell at every self-loop. This proves the coefficient identity for all possible excesses and for every pair of outlines. At $s=b=0$ it gives one for the empty diagram.

## Consequences for enumeration

The generating function is rational jointly in $z,u$, with denominator dividing $\det(I-zA-uB)$ and constant denominator coefficient one. Multiplication by this explicitly computable polynomial gives a finite constant-coefficient two-index recurrence outside its numerator support. For every fixed excess $b$, the series in $z$ is rational; explicitly its matrix factor is $(I-zA)^{-1}[B(I-zA)^{-1}]^b$. Taking a subsequence of admissible sizes $s=s_0+kw$ preserves constant-coefficient recurrence, for example by raising a finite recurrence matrix to its $w$th power. For a fixed cell count $s$, counting excess as a variable instead gives the matrix factor $(I-uB)^{-1}[A(I-uB)^{-1}]^s$.

The one-variable recurrence holds with excess fixed. The joint recurrence also covers varying excess. Along a diagonal one need not obtain a one-variable constant-coefficient recurrence. For example, a width-two chain of $2k$ cells with $2k$ extra entries has $\binom{4k-1}{2k}$ words and grows as $16^k/(2\sqrt{2\pi k})$.

The same construction gives the source exponential generating function at a prescribed diagram,

```math
\mathcal F^{D(p,q)}(t)=[z^s]\ e^\mathsf T\exp\!\big(t(zA+B)\big)v_y.
```

Each term of total word length $n$ receives $t^n/n!$; marking its discoveries by $z$ extracts exactly the required diagram. The expression uses the same finite matrices for every length at that width. At zero excess the construction specializes to the ordinary enumeration. Standard set-valued-tableau interpretations and fixed-poset ideal enumerations predate this problem. The bounded record of discoveries at the two diagram boundaries gives a single matrix formula for the whole growing periodic family. [Lam and Pylyavskyy](https://arxiv.org/abs/0705.2189)
