# Where a layered permutation can have a rank dip

Let $w=(w_1,\ldots,w_k)$ be a composition of $N$ and let $A_w(r)$ count its **distinct** generalized subwords of weight $r$. These are also the distinct length-$r$ patterns of the corresponding layered permutation. Put $c=(N+k-1)/2$.

**Theorem 1.** The ranks weakly decrease starting at $\lfloor c\rfloor$. They weakly increase through $\lceil N/2\rceil$ by the Pouzet–Rosenberg theorem. In particular, every possible failure of Vatter's Conjecture 2.6 is confined to an interval whose width depends only on the number of parts. [Conjecture 2.6](https://arxiv.org/pdf/2602.16355v4#page=7) · [First-half theorem](../principal-pattern-rank-unimodality/FirstHalf.lean)

**Theorem 2.** Fix any finite number of parts $k$. If $N\to\infty$, some fixed $\varepsilon>0$ satisfies $w_i/N\ge\varepsilon$ for every $i$ and $\max_i w_i/N\le1/2-\varepsilon$, then eventually $\lfloor c\rfloor$ is a peak. When $c$ is integral the peak is unique. When $c$ is half-integral the only other possible peak is $\lceil c\rceil$. Both assertions hold uniformly on each compact subset of the strictly balanced positive simplex. In particular, for **every** finite positive integer composition $a$, the principal ideals of $Ta=(Ta_1,\ldots,Ta_k)$ are unimodal for all sufficiently large integers $T$. This includes arbitrarily many ascents and descents. A dominant part is handled by the known monotone-interval criterion. [Dominant part](../principal-pattern-rank-unimodality/LONG-MONOTONE-INTERVAL.md)

## The leftmost embedding

A nonempty subword has a unique greedy embedding. To embed its next part, choose the first remaining position whose capacity is large enough. This succeeds for any embeddable word since each greedy index is at most the corresponding index in any embedding. For a fixed support $I=(i_1<\cdots<i_q)$, put $i_0=0$ and $b_h=\max(\{w_j:i_{h-1}<j<i_h\}\cup\{0\})$. The subwords with precisely this greedy support are the integer box
```math
b_h+1\le v_h\le w_{i_h},\qquad 1\le h\le q.
```
Empty boxes contribute zero, and the empty support gives the empty word. This counts distinct words exactly once. Write $I_{a,b}(x)=x^a+\cdots+x^b$ for $a\le b$ and zero otherwise. Each box contributes a product of interval polynomials. It is symmetric and unimodal about half the sum of the interval endpoints. To see this directly, the product of two symmetric consecutive strings decomposes into centered strings by (1) below. Induction gives the assertion for every box.

For any support of size $q$ the sum of the chosen upper endpoints and the $b_h$ is at most $N$. The gap maxima are charged to disjoint gaps among the skipped positions. Thus every box has center at most $(N+q)/2$. The full-support box and the box missing only the final position combine to give
```math
P(x)=\prod_{i<k}I_{1,w_i}(x)\,I_{0,w_k}(x).
```
This is centered at $c$. Every other nonempty box missing exactly one position is also centered at $c$. Indeed, the omitted position is immediately before a retained one and its whole capacity is the corresponding gap maximum. Every box omitting at least two positions is centered at or below $c-1/2$. Each summand consequently weakly decreases from $\lfloor c\rfloor$. This proves Theorem 1, including its half-integer case.

## Counting the strings that start near the middle

Write $s_i=w_i-1$ for $i<k$, $s_k=w_k$, and $S=\sum_i s_i=N-k+1$. Removing the common monomial $x^{k-1}$ from $P$ gives a product of the strings $[0,s_i]$. The elementary identity
```math
I_{0,a}(x)I_{0,b}(x)
   =\sum_{j=0}^{\min(a,b)}x^jI_{0,a+b-2j}(x) \tag{1}
```
follows by counting the pairs of degrees with a prescribed sum. A string $x^u[0,h]$ has width $h$ and center $u+h/2$. Applying (1) one factor at a time decomposes the entire product into strings centered at $c$. The multiplicity of the final width $h$ is the number of integer sequences $h_1=s_1,h_2,\ldots,h_k=h$ with
```math
|h_{i-1}-s_i|\le h_i\le h_{i-1}+s_i,\qquad
h_i\equiv \sum_{j=1}^{i}s_j\pmod 2. \tag{2}
```
For an integer $r$ with $r+1\le c$, the forward difference of $P$ at $r$ counts the strings starting exactly at $r+1$. It equals this multiplicity at width $h=2(c-r-1)$.

Here is a finite lower bound on this multiplicity. For $k\ge3$ put
```math
t=\min\left(\min_i s_i,\frac{S-2\max_i s_i}{k-2}\right).
```
Suppose $t\ge 2k+8$ and $0\le h\le k+2$ with $h\equiv S\bmod 2$. Subtract $t$ from all sides $s_i$. The resulting nonnegative lengths satisfy the closed polygon inequality because $S-2\max_i s_i\ge (k-2)t$. They can be arranged in the prescribed cyclic order to close a possibly degenerate plane polygon. For completeness, the attainable lengths of a sum of vectors with prescribed lengths $u_1,\ldots,u_m$ form the whole interval $[\max(0,2\max u_i-\sum u_i),\sum u_i]$. Induction follows by allowing the final vector's angle to range from zero to $\pi$, or from connectedness of the product of circles and the triangle inequality with the two endpoint configurations. Applying this to the first $k-1$ sides permits their sum to have exactly the last side's length.

Let $d_i$ be the length of the sum of its first $i$ edges. Then $d_1=s_1-t$, $d_{k-1}=s_k-t$, and $d_{i-1},s_i-t,d_i$ satisfy all three weak triangle inequalities. On adding $t$ to each length, every inequality has slack at least $t$. For $2\le i\le k-2$, choose any integer $h_i$ of the parity in (2) within $t/4$ of $d_i+t$. Each has at least $\lfloor t/4\rfloor$ choices. Put $h_{k-1}=s_k$ or $s_k+1$ with the required parity. The changes to any triangle side total at most $t/2+1<t$, so every triangle through index $k-1$ remains admissible. At the last step $|h_{k-1}-s_k|$ is zero or one with the parity of $h$, and $h\le k+2\le h_{k-1}+s_k$. This proves
```math
\#\{\text{strings of width }h\}\ \ge\ \lfloor t/4\rfloor^{k-3}. \tag{3}
```
For $k=3$ there are no intermediate choices and the right side equals one.

## Smaller supports and the peak

The other single-omission boxes, centered at $c$, all have nonnegative forward differences up to a step ending at or before $c$. For any box with $q\ge2$ parts, every forward difference has absolute value at most $(N+1)^{q-2}$. Multiplying its polynomial by $1-x$ cancels one interval factor to a difference of two monomials. Each coefficient of the product of the remaining $q-1$ factors is at most $(N+1)^{q-2}$ because fixing all but one value determines the last. The difference of two such nonnegative coefficients satisfies the same bound. For zero or one part the bound one suffices. There are at most $2^k$ supports.

For $k\ge4$, if
```math
t\ge2k+8,\qquad
\lfloor t/4\rfloor^{k-3}>2^k(N+1)^{k-4}, \tag{4}
```
then the positive contribution (3) strictly exceeds all negative contributions of boxes missing at least two positions. This holds in particular for every integer $r$ from $\lfloor N/2\rfloor-1$ through $\lfloor c\rfloor-1$, since $h=2(c-r-1)$ then has the needed parity and lies between zero and $k+2$. These steps increase strictly. Theorem 1 provides monotonicity before and after this interval. When $c$ is integral, the decrease from $c$ to $c+1$ is strict because (3) gives a width-zero string ending at $c$ and every other summand has weakly decreasing coefficients there. When $c$ is half-integral, (3) gives a width-one string ending at $\lceil c\rceil$, and the step following it decreases strictly. At the two central ranks all the centered summands tie and the smaller supports can only favor the lower rank.

Under Theorem 2's hypotheses $t$ is bounded below by a fixed positive multiple of $N$, so (4) holds eventually, uniformly under any fixed positive margins. For $k=3$, the boxes missing at least two positions have degree at most $\max w_i$, strictly below the central interval for all sufficiently large $N$. Apply (3) directly. Strict balance requires at least three parts. In the dilation corollary, whenever $2\max a_i\ge\sum a_i$ there is a monotone interval of length at least half the host at every dilation. This also covers one- and two-part hosts. ∎
