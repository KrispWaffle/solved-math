# Finitely many possible exceptions at any fixed number of parts

**Theorem.** For each positive integer $k$ there exists $N_k$ such that every composition of weight $N\ge N_k$ with exactly $k$ parts has a rank-unimodal principal ideal in generalized subword order. There is no minimum part-size assumption. The statement also holds for the principal permutation ideals of all layered hosts with exactly $k$ layers. For $k\ge4$ one may take $N_k=(64k^2)^{(k+2)^2}$. This makes the conjecture decidable for each specified number of parts. Vatter's conjecture for every finite composition remains open. [Original conjecture](https://arxiv.org/pdf/2602.16355v4#page=7) · [Rank window and a quantitative central estimate](PEAK.md)

We first give an exact finite criterion valid for **any** number of parts. Write $F_w(x)=\sum_r A_w(r)x^r$ for the distinct-subword rank polynomial, and set
```math
H=\lceil N/2\rceil,\qquad C=\lfloor(N+k-1)/2\rfloor.
```
The ranks weakly increase through $H$ and weakly decrease from $C$. It suffices for the forward differences at $r=H,\ldots,C-1$ to be nonincreasing. If the interval contains at most one difference there is nothing to prove. [Rank window](PEAK.md)

## Two largest parts

**Two-part criterion.** Let $k\ge2$, and let $t$ be the sum of the two largest parts, counted with multiplicity. If
```math
t\ge\max\bigl(\lfloor N/2\rfloor+1,C-1\bigr),
```
then the entire rank sequence is unimodal.

By reversing the composition if necessary, write it as $X,L,Y,M,Z$, where $M\ge L$ are two largest parts. Let $A=F_X$, $B=F_Y$, $D=F_Z$, and write $S_T=x+\cdots+x^T$. The peak identity for arbitrary arms $U,V$ with a separating maximum $T$ is
```math
F_{U,T,V} = F_U + F_V +(S_T-1)F_UF_V.
```
To verify the identity, greedily embed the longest prefix of a given word into $U$. If a letter remains, it can be placed at the maximum $T$ precisely when it is at most $T$. It is the first letter that fails to extend the prefix in $U$. The remaining suffix may be any subword of $V$. The prefix together with the failing letter belongs to the difference of the two ideals of $U,T$ and $U$. Its polynomial is $1+S_TF_U-F_U$, because a nonempty word embeddable in $U,T$ can place its last letter in $T$. This gives the claimed identity. Zhang and Zhang use this decomposition for their arm families. [Peak decomposition, §4](https://arxiv.org/pdf/2611.28619#page=5)

Define
```math
E_D=(1-x)(1-D)+xD,\qquad E_{A,B}=(1-x)(A+B-AB)+xAB.
```
Both have nonnegative coefficients. The coefficient of degree $j\ge2$ in $E_D$ is $2D_{j-1}-D_j\ge0$. Every composition of weight $j$ has a parent of weight $j-1$ obtained by removing a terminal one or decrementing the final part. The parent still belongs to the ideal and has at most two children. The constant coefficient of $E_D$ is zero and its linear coefficient is $1-D_1\ge0$. For $E_{A,B}$, for each fixed degree $j$ choose a finite middle capacity $T>2j+|X|+|Y|$, where bars denote total weight. Then the degree-$j$ coefficient equals that of $(1-x)F_{X,T,Y}$. It is nonnegative by the known first-half theorem.

Twice applying the peak identity and using $(1-x)S_T=x-x^{T+1}$ now gives
```math
(1-x)^2 F_w=(1-x)^2D+
       (E_D-x^{M+1}D)(E_{A,B}-x^{L+1}AB). \tag{1}
```
The two unshifted terms have degree at most $N-t+2$. The doubly shifted term starts in degree $t+2$. The two singly shifted terms have nonpositive coefficients. Therefore the coefficients of $(1-x)^2F_w$ are nonpositive at all integer degrees strictly between $N-t+2$ and $t+2$. The hypothesis places every degree in $[H+2,C]$ in this range. These coefficients are precisely the second differences comparing consecutive unknown forward differences. This proves the criterion.

## An explicit cutoff for every number of parts

If $k\le3$ there is at most one forward difference between the known increasing and decreasing ranges. Hence assume $k\ge4$. Set
```math
Q=64k^2,\qquad N_k=Q^{(k+2)^2},\qquad N\ge N_k .
```
These generous constants make all comparisons below uniform. We will use integer string decompositions and nonnegative coefficients throughout. The resulting bound also gives a terminating decision procedure for any specified $k$.

Suppose the two-part criterion does not already apply. With $M,L$ as above, this gives $M+L<N/2+k/2$. As $L\ge(N-M)/(k-1)$, we obtain
```math
N-2M\ \ge\ \frac{N-k(k-1)}{k-2}\ \ge\ \frac{N}{2k}.
\tag{2}
```
At least four parts are at least $N/Q$. Otherwise the sum of the largest three is at most $3(M+L)/2$, and all remaining parts together are less than $kN/Q$. These two bounds sum to less than $N$.

Write $u_j=N/Q^{j+1}$. Some interval $[u_{j+1},u_j)$ for $0\le j\le k$ contains no part, since the $k+1$ intervals are disjoint. Set $u=u_j$ and call the $b\ge4$ indices of size at least $u$ large. All other parts have total weight $E\le ku/Q$. In particular
```math
u\ge N/Q^{k+1},\qquad E\le u/(64k),\qquad u\ge 128(k+2).
\tag{3}
```
Let $U$ be the product of the sizes of the small parts, using one for an empty product.

In each greedy box, fix all chosen coordinates at small indices. Each support then produces at most $U$ fixed assignments. Full support produces exactly $U$. A box retaining every large index has an interval from $1+e_i$ to $w_i$ at each large part, where $e_i$ is the maximum of the preceding skipped gap. The gaps contain only small parts. Together their maxima and the sum $d$ of the fixed small values satisfy $\sum e_i+d\le E$. The box of remaining variables, including the monomial shift by $d$, therefore has center $c'$ with
```math
N-E \ \le\ 2c'=N-E+b+\sum e_i+2d \ \le\ N+b+E.
```
Every remaining width $w_i-e_i-1$ is at least $u-E-1$. For $H+2\le r\le C$, inequality (3) gives $|2r-2c'|\le 2E+2k+2<u-E-2$.

Use the backward difference $\nabla G_y=G_y-G_{y-1}$ for coefficients. After splitting off one large interval, the frozen box polynomial has the form $x^a[0,m](x)G(x)$ with $G$ a product of zero-based intervals of total degree $g$. Put $y=r-a$. Its second difference is
```math
\nabla G_y-\nabla G_{y-m-1}.
```
Since $2c'=2a+m+g$ and $|2r-2c'|< m-1$, $y$ lies strictly on the falling side of the symmetric product $G$, and $y-m-1$ lies on its rising side. Both signs follow from its centered string decomposition. Every frozen box retaining the large indices thus contributes a nonpositive second difference throughout the central window.

For a full-support box take the removed interval at the largest part, so $m=M-1$. The nonnegative quantity $-\nabla G_y$ counts the strings of $G$ ending at $y-1$. They have width
```math
h=2(y-1)-g,\qquad h\equiv g\pmod2,\qquad |h-m|\le 2E+2k+4 .
```
There is a uniform lower bound on their number. The $b-1$ widths of $G$ and the integer $h$ are the side lengths of a closed polygon. In fact their least side is at least $u/2$, by (3). Their sum minus twice their largest side is at least $N-2M-E-k-|h-m|\ge N/(4k)$ by (2)–(3). Here replacing a single length by another changes this last expression by at most the absolute change, as it is the minimum of the signed sums with one negative sign.

Subtract $u/4$ from all $b$ sides. All lengths stay nonnegative and the new polygon slack remains nonnegative, since $(b-2)u/4\le ku/4\le N/(256k)$. Close a polygon with these lengths in their prescribed order. On restoring $u/4$ to each side and each intermediate diagonal, every triangle inequality in the successive coupling of the first $b-1$ sides has slack at least $u/4$. Keep the first side and the last diagonal $h$ fixed. Each of the $b-3$ intermediate diagonals may now be chosen independently within distance $u/16$ of its restored length, with the parity prescribed by the preceding sides. There are at least $\lfloor u/16\rfloor$ choices of each parity. The total change within a triangle is at most $u/8$. Each path therefore contributes a separate centered string of width $h$ by the two-string multiplication identity. This proves that the full-support contribution to the central second difference is at most
```math
-U\lfloor u/16\rfloor^{b-3}.
\tag{4}
```
The polygon closure and the correspondence from integral diagonal paths to distinct string summands are proved in the peak-location argument. [String identity and polygon paths](PEAK.md)

If a support misses a large coordinate, at most $b-1$ large coordinates survive freezing. The absolute second difference of each such box is at most $4(N+1)^{b-4}$. For at least three variables this follows by canceling two geometric-series denominators and fixing all but one of the remaining variables in each of the four resulting translates. With zero, one or two variables the bound four suffices. All these supports together contribute at most
```math
4\cdot 2^k U (N+1)^{b-4}.
\tag{5}
```
The magnitude in (4) exceeds (5). Indeed, let $J=Q^{k+1}$, so $\lfloor u/16\rfloor\ge N/(32J)$. Using $N+1\le2N$, the required inequality follows from $N>2^{k+6b-17}J^{b-3}$. This holds for $b\le k$ and $N\ge Q^{(k+2)^2}$: the difference $(k+2)^2-(k+1)(b-3)$ is at least $6k+7$, and $Q\ge 2^{10}$.

Consequently all the second differences in the unresolved central window are strictly negative in this case. The two-part criterion handles the complementary case with weak nonpositivity. The first-half and upper-tail inequalities finish the proof. ∎

## How to decide a fixed number of parts

For a specified $k\ge4$, enumerate the finitely many positive compositions of weights below $N_k$ having exactly $k$ parts and use the greedy-box formula or peak recurrence to compute each rank sequence exactly. The existence of any larger counterexample has been excluded analytically. This is a termination guarantee. No enumeration up to this bound is asserted. Expressed contrapositively, a counterexample of weight $N$ must have a number of parts growing at least on the order of $\sqrt{\log N/\log\log N}$ as $N$ grows.
