# Every real number in the unit interval is a derangement limit

**Theorem.** For each real $p\in[0,1]$ there is an infinite hereditary class $\mathcal C$ of permutations for which the fraction of members of length $n$ with no fixed points converges to $p$. One may require the growth rate of the class to lie in a single fixed interval strictly between two and three, including at the two endpoints $p=0,1$.

This answers the attainable-values question immediately after Question 4.3 in Vatter’s published paper. Write $a_n(\mathcal C)=|\mathcal C_n|$ and $d_n(\mathcal C)$ for the number of derangements there. Each distinct permutation has weight one. Take the empty permutation to be a derangement. [Original question, §4](https://arxiv.org/pdf/2602.16355v4#page=18)

## Two classes with the same growth rate

Vatter’s Proposition 3.3 supplies a nontrivial closed interval $[r_0,r_1]\subset(2,3)$ with the following property. For every $r$ in the interval there is a sum-closed permutation class $\mathcal A_r$ of growth rate $r$ whose number $s_j$ of sum-indecomposable members of length $j$ is bounded independently of $j$. Indeed, the proof realizes the entire interval between the growth rates for two bounded sequences of indecomposable counts. For instance, take $r_0=5/2$ and $r_1=13/5$. The two extremal indecomposable series from that proof have values $614/625<1$ at $2/5$ for the lower series and $31335/28561>1$ at $5/13$ for the upper series. Their positive roots at value one therefore enclose the proposed reciprocal interval. The singleton is present. [Vatter, Proposition 3.3 and proof](https://arxiv.org/pdf/0807.2815#page=8)

Fix $r$ and put $R=1/r$, $S(z)=\sum_{j\ge1}s_jz^j$ and $a_n=a_n(\mathcal A_r)$. Direct-sum factorization is unique, so $A(z)=\sum a_nz^n=1/(1-S(z))$. Vatter’s Proposition 2.2 gives $S(R)=1$. Since the $s_j$ are bounded, $S$ is analytic on the open unit disk. The zero of $1-S$ at $R$ is simple. There are no other zeros on $|z|\le R$: inside, $|S(z)|<1$, and equality $S(z)=1$ on the circle forces every nonzero term to have positive real phase, including $s_1z=z$. Isolated zeros and compactness now give a larger disk on which $A$ has just this pole. Subtracting its simple-pole term and using the Cauchy coefficient estimate gives constants $c=1/(RS'(R))>0$ and $0<r'<r$ such that
```math
a_n=c r^n+O((r')^n).
```
A singleton summand is a fixed point. Members with no singleton summand have series $1/(1-S(z)+z)$, whose denominator stays positive on a real interval beyond $R$ and whose series converges there by the nonnegative geometric expansion. In particular $d_n(\mathcal A_r)/a_n\to0$ exponentially fast. [Vatter, Propositions 2.1–2.2](https://arxiv.org/pdf/0807.2815#page=3)

Define $\mathcal B_r=\mathcal A_r\ominus\mathcal A_r$ to consist of skew sums, allowing an empty factor. In a skew sum the left block lies above the right block. Selecting a subsequence simply selects patterns independently in the blocks, so $\mathcal B_r$ is hereditary. Write $b_n=a_n(\mathcal B_r)$. Counting marked splits initially gives $\sum_{m=0}^n a_m a_{n-m}=c^2 n r^n+O(r^n)$ by the exponential estimate. A direct-decomposable permutation is skew-indecomposable: a proper direct cut places all values on its left below all to its right, which is incompatible with a proper skew cut, by comparing the first and last entries. A split into two nonempty skew-indecomposable factors is unique, by the unique skew decomposition (the direct decomposition after complementing values). All pairs not covered by this uniqueness have an empty or direct-indecomposable factor. With $s_j$ bounded and $a_j=O(r^j)$, there are $O(r^n)$ such pairs in total. This proves
```math
b_n=c^2 n r^n+O(r^n).
```
Also, a skew sum of two positive lengths is direct-indecomposable. Every direct-decomposable member of $\mathcal B_r$ therefore belongs to $\mathcal A_r$, giving only $O(r^n)$ such members.

Almost every member of $\mathcal B_r$ is a derangement. In a direct sum every position and its value lie in the same direct summand. Within a summand of length $j$ their distance is at most $j-1$. The number of members of $\mathcal A_r$ of length $m$ with a summand of size at least $L$ is at most
```math
\sum_{j=L}^{m}s_j\sum_{u+v=m-j}a_ua_v
     \le K (m+1)r^{m-L}.
```
Here the left sum counts a marked offending summand, and the estimate uses $a_t\le K_0r^t$ and a geometric tail. In a split $m+(n-m)$ with both lengths at least $L$ and no summand of either factor of size at least $L$, the positive and negative shifts $n-m$ and $-m$ preclude a fixed point. Over all splits, the smaller lengths below $L$ contribute $O(Lr^n)$ pairs, and a large summand contributes $O(n^2r^{n-L})$ pairs. Taking $L=\lceil 3\log_r(n+1)\rceil$ gives
```math
0\le b_n-d_n(\mathcal B_r)=O((1+\log n)r^n).
```
Counting pairs gives an upper bound even for permutations with more than one split.

## Weight of a finite direct-sum suffix

Let $\mathcal F$ be a finite hereditary class containing the empty permutation. Write $f_j=a_j(\mathcal F)$ and $h_j=d_j(\mathcal F)$, and put $F(z)=\sum f_jz^j$ and $H(z)=\sum h_jz^j$. The class $\mathcal C=\mathcal B_r\oplus\mathcal F$ is hereditary. Its derangement limit is
```math
\frac{H(1/r)}{F(1/r)}.
\tag{1}
```
Indeed, if the first factor is direct-indecomposable and nonempty, the first component of the unique direct decomposition recovers it. The suffix is then uniquely determined. With $j$ bounded by the maximum length in $\mathcal F$, all representations with a direct-decomposable first factor account for only $O_{\mathcal F}(r^n)$ pairs. Thus one may count pairs with an error of that order. The counts of all pairs and of deranged pairs are respectively $\sum_j b_{n-j}f_j$ and $\sum_j d_{n-j}(\mathcal B_r)h_j$: a direct sum is fixed-point-free exactly when both factors are. Divide by $c^2nr^n$ and use the finite number of shifts. The normalized limits are $F(1/r)>0$ and $H(1/r)$, proving (1). This also gives growth rate $r$ for the decorated class.

## Interpolating to a prescribed real number

Fix $0<p<1$. For integers $M,N$ take the finite hereditary union
```math
\mathcal F_{M,N}
=(\mathcal B_{r_0})_{\le M}\ \cup\ (\mathcal A_{r_1})_{\le N}.
```
Each permutation in the union is counted once. For a finite class write $W_z$ for its total weight with a member of length $j$ receiving weight $z^j$, and $W_z^\circ$ for its derangement weight.

At $z_1=1/r_1$, the total weight of the entire $\mathcal B_{r_0}$ is finite since $r_0<r_1$. The total weight of $(\mathcal A_{r_1})_{\le N}$ grows linearly in $N$, while its derangement weight stays bounded by the exponential estimate above. Therefore the derangement fraction in the union at $z_1$ tends to zero as $N$ increases, uniformly in $M$. Choose $N$ so this fraction is less than $p$ for every $M$.

Keep that $N$ fixed. At $z_0=1/r_0$ the truncated weight of $\mathcal B_{r_0}$ grows on the order of $M^2$, while its weight of members with a fixed point is $O(M\log(M+2))$. The second class in the union contributes at most a fixed finite additional weight. Thus for some $M$ the derangement fraction in the union at $z_0$ exceeds $p$. Both bounds use ordinary union inequalities and allow overlap of the finite classes.

For this one fixed $\mathcal F_{M,N}$ the function $H(z)/F(z)$ is continuous on $[z_1,z_0]$, since the denominator is at least its empty term one. The intermediate value theorem supplies $z$ in the interval with ratio exactly $p$. Set $r=1/z$ and take the class $\mathcal B_r\oplus\mathcal F_{M,N}$ from (1). Its limit is $p$. The endpoint values zero and one are realized by $\mathcal A_{r_0}$ and $\mathcal B_{r_0}$ respectively. Every finite-length fraction lies in $[0,1]$, completing the characterization. ∎
