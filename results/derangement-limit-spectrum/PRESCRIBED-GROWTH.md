# Prescribing the derangement limit and the growth rate together

**Theorem.** For every real $g\ge\lambda_B$ and every $p\in[0,1]$, there is a hereditary permutation class $\mathcal C$ such that
```math
|\mathcal C_n|\sim Cn^d g^n,\qquad
\frac{|\{\pi\in\mathcal C_n:\pi\text{ has no fixed point}\}|}{|\mathcal C_n|}\longrightarrow p
```
for some $C>0$ and integer $d\ge0$. Here $\lambda_B\simeq2.35698$ is Bevan's constant, the positive root of $x^8-2x^7-x^5-x^4-2x^3-2x^2-x-1$. The growth rate is the ordinary limit of $|\mathcal C_n|^{1/n}$. Both limits hold along all positive lengths. [Bevan, Theorem 2](https://arxiv.org/pdf/1410.3679#page=2) · [Vatter's attainable-values question](https://arxiv.org/pdf/2602.16355v4#page=18)

The proof also gives a sum-closed class of every growth rate on the entire ray $[\lambda_B,\infty)$, with a bounded number of direct-indecomposable permutations at each length. Vatter's Conjecture 10.1 asks whether the upper growth rate of every permutation class is the ordinary growth rate of a sum-closed class. The theorem establishes its full finite upper ray. The remaining question concerns rates between their uncountability threshold $\xi$ and $\lambda_B$. The construction here also gives the joint conclusion at any $g>\kappa$ having a carrier of the following kind, where $\kappa$ is the positive root of $x^3-2x^2-1$. [Vatter, Conjecture 10.1](https://arxiv.org/pdf/1605.04297#page=35) · [Pantone–Vatter, concluding remarks](https://arxiv.org/pdf/1605.04289#page=28)

## Two sufficient ingredients

Set $z=1/g$. We will use a sum-closed hereditary class $A$ whose indecomposable generating function $S$ is analytic on a disk of radius greater than $z$, with $S(z)=1$ and a singleton summand. We also use a family of hereditary classes $F_t$ at a common strictly smaller exponential growth bound. With a size-$j$ permutation weighted by $z^j$, their deranged weight is a fixed $H>0$ and their total weight is $Z+t$, where every $0\le t\le\delta$ occurs for some fixed $\delta>0$. An upper growth bound smaller than $g$ suffices for the family; no asymptotic enumeration of its members is needed.

The simple-pole and singleton arguments of the original proof give $|A_n|=c g^n+O((g')^n)$ and $d_n(A)=O((g')^n)$ with $g'<g$. There are $O(h^j)$ indecomposable members at size $j$ for some $1<h<g$. Marking a large direct summand gives at most $C(n+1)g^n(h/g)^L$ members of size $n$ with a summand of length at least $L$. In all others each position is within $L$ of its value. [Counting and displacement estimates](PROOF.md)

Let $K\ge5$ and let $\tau$ be a simple permutation of size $K$. An inflation of $\tau$ replaces its entries by consecutive position and value blocks. Allow empty blocks when forming the hereditary class $\tau[A,\ldots,A]$. For positive block sizes the standard substitution decomposition gives unique factors and unique simple quotient $\tau$. The number of positive representations at length $n$ is
```math
Q n^{K-1} g^n+O(n^{K-2}g^n),\qquad Q=\frac{c^K}{(K-1)!}.
```
Indeed, sum the products $\prod |A_{m_i}|$ over positive compositions of $n$. Replacing a factor $c g^{m_i}$ by its exponentially smaller error loses one free size variable after summing the geometric series. The number of representations with at least one empty block is $O(n^{K-2}g^n)$. [Albert–Atkinson–Klazar, decomposition and abundance of simple permutations](https://cs.uwaterloo.ca/journals/JIS/VOL6/Albert/albert.pdf)

Almost every positive representation is a derangement. In cell $i$ the displacement is shifted by
```math
L_i(m)=\sum_{\tau(j)<\tau(i)}m_j-\sum_{j<i}m_j.
```
The coefficient of $m_i$ is zero. Another coefficient is $1$ or $-1$: otherwise the predecessors in position and value agree, so $\tau(i)=i$ and the permutation is a direct sum at a proper boundary. This contradicts simplicity for $K\ge4$, including an endpoint singleton. Fix all sizes except $m_i$ and a cell with a nonzero coefficient. Their sum is prescribed; the inequality $|L_i(m)|\le L$ permits at most $2L+1$ choices. Thus at most $O((L+1)n^{K-2})$ compositions lie in this slab, each of weight $O(g^n)$. The large-direct-summand estimate, summed over all cells and compositions, contributes $O(n^K g^n(h/g)^L)$. Taking a sufficiently large constant times $\log(n+1)$ for $L$ shows that a proportion tending to one avoids every fixed point. A positive inflation of this simple permutation is direct-indecomposable.

## Combining simple quotients

Use different simple permutations to distinguish the following families. All component classes include the empty permutation. Their unions are hereditary because any subsequence restricts separately to the inflation cells or to the direct-sum blocks.

- A simple quotient of size $K$ filled with $A$ contributes leading coefficient $Q$ to both the total count and the deranged count, on the common scale $n^{K-1}g^n$.
- One $A$ prefix direct-summed with a simple quotient of size $K-1$ filled with $A$ contributes $Q$ to the total and zero to the deranged leading coefficient. With all cells positive its right factor is the last direct-indecomposable component. This recovers both factors uniquely. A derangement requires a deranged prefix; the exponentially small bound for its counts saves one free size, giving $O(n^{K-2}g^n)$ derangements.
- A third simple quotient of size $K$ filled with $A$, followed in direct sum by $F_t$, contributes $Q(Z+t)$ to the total and $QH$ to the deranged count. For positive core cells its direct-indecomposable prefix is uniquely recovered as the first component. Summing over suffix lengths uses dominated convergence with the summable weights $|F_{t,j}|g^{-j}$, because the core counts at length $m$ are $O((m+1)^{K-1}g^m)$. Empty core cells cost one power of $n$ after the same convolution.

For two positive cores of the first or third kind, their first direct components recover their distinct simple quotients. Two families of the second kind are distinguished by their last components. A positive member of the first kind is direct-indecomposable, whereas the positive second kind is direct-decomposable. Any overlap between positive representatives of the second and third kinds forces the simple inflation at the start of the third kind to be the first direct component of the $A$ prefix in the second. It is then a sum-indecomposable member of $A$. Its length-$j$ count is $O(h^j)$, and the following suffix belongs to $F_t$ of strictly smaller growth than $g$. Their convolution is exponentially smaller than $g^n$ up to a polynomial factor. These estimates justify addition of the leading coefficients for distinct permutations, including possible empty suffixes.

Choose $a$ families of the first kind, $b$ of the second, and $M$ of the third with the same $F_t$. The class has limiting fraction
```math
\frac{a+MH}{a+b+M(Z+t)}.
\tag{1}
```
For $0<p<1$, choose a positive integer $M$ with $1/M<\delta$ and a nonnegative integer $a$ large enough that $T=(1-p)a/p+M(H/p-Z)\ge0$. Put $b=\lfloor T\rfloor$ and $t=(T-b)/M$. Equation (1) is exactly $p$. There are enough distinct simple permutations at both sizes $K$ and $K-1$ for sufficiently large $K$, by their asymptotic enumeration. A single family of the second or first kind realizes zero or one.

## Independent choices of bounded exponential growth

Let $g>\kappa$ and choose the least $s\ge2$ for which $d=(s!)^2\ge g-1$. In Vatter's sequence of oscillations there is one simple base permutation $\sigma_k$ for each $k\ge4$. Its inversion graph is a path. Inflate the two endpoints by an ordered pair $\alpha,\beta$ of arbitrary size-$s$ permutations. Use Vatter's prescribed left and right endpoints for each parity of $k$. Write $U_s$ for the resulting set. Vatter's Proposition 3.2 implies that it is an antichain of sum-indecomposable permutations. For distinct ordered decorations at least one pair of same-length entries is incomparable. At a fixed base length uniqueness of the simple quotient and its inflation distinguishes all $d$ tags. Thus there are $d$ at every length $j\ge J=2s+2$. [Vatter, definition preceding Proposition 3.2 and proposition](https://arxiv.org/pdf/0807.2815#page=8)

Write $V_s$ for the downward closure of $U_s$. Any of its members can be reduced, by deleting at most $2(s-1)$ entries, to a subpattern of an increasing oscillation. Keep one representative of each nonempty endpoint decoration. The reduced permutation has a linear forest for its inversion graph. A connected inversion graph characterizes direct-indecomposability, and the permutations with path inversion graphs are exactly the increasing oscillations. There is one at each of sizes one and two and two at every size at least three. The sum closure of these paths consequently has generating function
```math
\frac{1}{1-z-z^2-2z^3/(1-z)}=\frac{1-z}{1-2z-z^3}.
```
Its growth rate is $\kappa$. To reinsert $j$ deleted entries in an $n$-permutation there are at most $\binom nj^2j!$ choices of positions, values, and their pairing. Thus $V_s$ is bounded in size by a polynomial times $\kappa^n$ for fixed $s$. In particular it has a strictly smaller exponential growth bound than $g$. [Brignall–Vatter, Propositions 1.14, 1.16 and 1.17](https://www.rbrignall.org.uk/papers/lwqo-for-pp.pdf#page=10) · [Enumeration of the oscillations](https://www.rbrignall.org.uk/papers/lwqo-for-pp.pdf#page=27)

For the suffix classes $F_t$, take the proper-pattern downset of the tags $1\oplus u$ for $u\in U_s$, and adjoin any chosen subset of those tags. They are incomparable because an occurrence of a sum-indecomposable $u$ of size at least two in $1\oplus u'$ must lie in $u'$. Adding tags preserves heredity and changes only the total weight, since every tag fixes its first position. All suffix permutations lie in $(\{\varepsilon,1\})\oplus V_s$. Their common deranged weight $H$ includes the empty permutation. The total can increase by every value in
```math
[0,\delta],\qquad \delta=\frac{d z^{J+1}}{1-z},\qquad z=1/g.
```
Indeed, the changes are sums $\sum_{j\ge J+1}e_j z^j$ with each $e_j\in\{0,\ldots,d\}$. In the unshifted digit interval $[0,d/(1-z)]$, the possible first digits leave overlapping or touching closed intervals precisely when $d z/(1-z)\ge1$. Iterating and bounding the discarded remainder by $z^m d/(1-z)$ proves the series representation, including both endpoints. The greedy digit principle used in earlier growth-rate constructions is also kernel-checked here. [Bevan, §2](https://arxiv.org/pdf/1410.3679#page=4) · [Lean proof of the digit and residual intervals](../../lean/SolvedMath/DerangementGrowth.lean)

## A sum-closed carrier on the upper ray

For $\lambda_B\le g\le13/4$ use Bevan's five families in the proof of Theorem 2, spanning $[\lambda_B,\lambda_A]$, and Vatter's Propositions 3.3–3.4, spanning $[\lambda_A,\lambda_A+1]$, where $\lambda_A\simeq2.48187$. These constructions use bounded indecomposable counts. Their generating functions therefore satisfy the required analytic condition at $1/g$. Vatter's subsequent horizontal juxtaposition gives growth rates for general classes. [Bevan, proof of Theorem 2](https://arxiv.org/pdf/1410.3679#page=16) · [Vatter, Propositions 3.3–3.4](https://arxiv.org/pdf/0807.2815#page=8)

There is a finite indexing detail in the preprint of Proposition 3.3. Its chosen oscillation bases start at length four, so decorating both endpoints by size two first gives tags of length six. The two independent length-five choices used in the proof can be supplied by $23451$ and $51234$. Their inversion graphs are the degree-four star, whereas the two cited tag families have maximum degree three. Their only proper length-four indecomposable patterns are respectively $2341$ and $4123$, both already present in the first $12,12$ tag $412563$. Their shorter indecomposable patterns are also present there. Thus these additions supply the stated choices at size five independently of the extra length-four choices. In Proposition 3.4, adjoining all indecomposables through size six as prescribed gives the upper sequence $1,1,3,13,71,461,11,11,\ldots$. The printed line omits its size-five coefficient. At $4/13$ the lower and corrected upper weights for that step are $2713076/3341637<1<52018532/43441281$. [Preprint construction](https://arxiv.org/pdf/0807.2815#page=8) · [Exact finite check](verify_growth.py)

Now suppose $g\ge13/4$ and use $s,d,J$ from the preceding section. Let $I_0$ be all nonempty sum-indecomposable proper patterns of tags in $U_s$. Write $I_m$ for its union with all sum-indecomposables of length at most $m$, and $I_m(z)$ for the corresponding sum of length weights. For $j\ge J$ the number of indecomposable patterns of length $j$ in $V_s$ is at most
```math
B_s=2\left(\sum_{i=1}^{s}i!\right)^2.
```
To see this, compress each retained endpoint decoration to one point. The compressed length is at least $j-2(s-1)\ge4$. Its inversion graph is connected, because it is a quotient of the connected graph of the original pattern by the retained blocks. The surviving base vertices therefore induce a connected subpath. Any decorated original path endpoint that survives is still an endpoint of this subpath. Order its endpoints by position and record the two endpoint patterns, using size one for an undecorated endpoint. Their lengths and $j$ determine the compressed size, which permits at most two oriented oscillations. These three choices reconstruct the permutation and give the claimed bound.

We claim $I_{J-1}(z)<1$. At $s=2$, unique direct decomposition gives $1,1,3,13,71$ indecomposables in sizes one through five. In general these counts obey $c_n=n!-\sum_{i=1}^{n-1}c_i(n-i)!$. The initial weight is bounded by $\sum_{j=1}^5 c_jz^j+18z^6/(1-z)$, which at $z=4/13$ is $306004/371293<1$. At $s=3$ minimality gives $g>5$. The bound $\sum_{j=1}^7 j! z^j+162 z^8/(1-z)$ is at most $80611/156250<1$ at $z=1/5$. For $s\ge4$, minimality gives $g>1+((s-1)!)^2\ge 4s+2$. The first $2s+1$ factorial terms sum to at most $2/g$ by successive term ratios. Also $\sum_{i=1}^s i!\le2s!<2s\sqrt{g}$. The remaining weight is thus at most $8s^2 g^{-(2s+1)}/(1-1/g)<1/g$, since $g>4s+2$ and $s\ge4$. The sum is below one in all cases. [Rational checks](verify_growth.py)

The weights $I_m(z)$ eventually exceed one. At length $j\ge2$ alone, $(j-1)!$ permutations beginning with their maximum are sum-indecomposable. Choose the first $m\ge J$ for which $I_m(z)\ge1$. Include $I_{m-1}$ and as many additional size-$m$ elements as possible without passing one. Their proper indecomposable patterns lie in $I_{m-1}$. The residual is in $[0,z^m)$. At every size $j>m$ we can freely choose zero through $d$ tags from $U_s$ because all their proper indecomposable patterns lie in $I_0$. The digit interval beginning at $m+1$ has length $d z^{m+1}/(1-z)\ge z^m$, so some choice fills the residual exactly.

The chosen indecomposables form a set $I$ that is downward closed among indecomposables and contains the singleton. Direct sums of arbitrary sequences of elements of $I$ form a hereditary class $A$. A subpattern of any selected summand is the direct sum of indecomposable subpatterns of that summand. Uniqueness of direct decomposition shows that the indecomposables of $A$ are exactly $I$. Their counts are bounded by $B_s$ for all sufficiently large sizes, and their generating function $S$ satisfies $S(1/g)=1$. This supplies the required carrier. Together with the suffix classes and equation (1), it proves the joint assertion on the whole ray. ∎

## Formal verification

Lean proves that every cell of a nontrivial sum-indecomposable permutation has an active displacement coefficient, and that the fixed-total slab on each indicated fibre has at most $2L+1$ integer points. It proves the digit-series expansion, the residual filling lemma and the exact mixture identity. The conditional final statement uses the original class definitions and both ordinary limits. The inflation asymptotics, tag estimates, and carrier construction above are written proofs. [Lean declarations](../../lean/SolvedMath/DerangementGrowth.lean) · [Independent review](AUDIT.md)
