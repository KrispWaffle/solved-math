# The size of a rare connectivity gap

Let $d$ and $\kappa$ be the minimum degree and vertex connectivity of the inversion graph of a uniform permutation of $[n]$. For every fixed integer $r\ge1$ and real $x\ge0$,
```math
n^r\Pr\{d-\kappa\ge r,\ d>x\sqrt n\}\longrightarrow e^{-x^2}.
```
In particular $\Pr(d-\kappa\ge r)\sim n^{-r}$. Conditional on this rare event, the scaled minimum degree has the same Rayleigh limit as in the unrestricted permutation. The result follows by identifying which separating configurations have probability of order $n^{-r}$. [Scanline representation](PROOF.md) · [Two-point case and corner estimates](EXCEPTIONS.md) · [Unconditional degree limit, Bhattacharya–Mukherjee](https://arxiv.org/abs/1503.03582)

## The smallest possible side

Write $m=r+1$. A separating rectangle with crossing count $c\le d-r$ and $A$ southwest vertices satisfies $d\le c+A-1$, by counting the possible neighbors of any vertex on that side. Thus $A\ge m$. At a point $(a,b)$ southwest of thresholds $i,j$, we also have $d\le a+b-2$ and $c=i+j-2A$. Hence
```math
(i-a)+(j-b)\le 2A-r-2.
```
If $A=m$, this bound is $r$. The $m$ row deficits are distinct nonnegative integers, so their sum is at least $m(m-1)/2$. The same holds for the column deficits. The upper bound on their combined sum is $mr=m(m-1)$. Equality forces both lists to use exactly $0,\ldots,r$, with each point’s two deficits summing to $r$. Thus the rectangle contains a consecutive decreasing block
```math
\pi(p+h)=v+r-h\quad(0\le h\le r),\qquad i=p+r,\quad j=v+r .
```
Every vertex of the block has degree $c+r=d$, since its degree lies between $d$ and $c+m-1$. The same argument works at the other diagonal corner after reversing both orders.

## Controlling the contribution from larger corners

Use the localization proof with $b=\lceil\sqrt{(r+2)n\log n}\rceil$. Its first empty square has probability at most $n^{-r-2}$, and its other failure probabilities are exponentially small in $b$. It puts one side of every relevant cut in an oriented diagonal corner of side $O_r(\sqrt{n\log n})$. [Localization proof](PROOF.md#localizing-the-thresholds)

Use dyadic $s\le i+j<2s$ and let $Y$ count points in the square $[2s]^2$. The event $E_s$ that $Y\ge s/4$ or the square $[\lfloor s/4\rfloor]^2$ is empty is necessary, since otherwise $c>s/2$ and a point of the smaller square has degree below $s/2$. Mark $m$ points in the southwest rectangle. Conditional on their prescribed positions and values, the remaining permutation is uniform on $n-m$ points. The empty-square and row-choice estimates in the two-point proof give
```math
\Pr(E_s\mid\text{prescriptions})\le C_r e^{-c_r s^2/n}.
```
Indeed at least $\lfloor s/4\rfloor-m$ small rows and columns remain when the prescription permits emptiness. For the other alternative, $u$ further hits have probability at most $(C_r s^2/(nu))^u$, by choosing their rows. Bounded $s$ is covered by enlarging $C_r$.

Both coordinate spans of the marked points are at most $2Y$. Choose their two coordinate minima in $O(s^2)$ ways, then specify the other $r$ offsets in each coordinate and their matching. For maximum offset $h\ge1$, this gives $O_r((h+1)^{2r-1})$ choices per pair of minima. Write $\mu=1+s^2/n$. The sum of these offset counts weighted by $\Pr(2Y\ge h\mid\text{prescriptions})^{1/2}$ is $O_r(\mu^{2r})$: sum the polynomial up to a sufficiently large multiple of $\mu$, and use the row-choice bound, which decays geometrically in $h$, above that point. The conditional law of $Y$ depends only on $n,s,m$. Applying Cauchy–Schwarz to this event and $E_s$, and multiplying by the probability $1/(n)_m$ of each prescription, bounds the contribution from the scale by
```math
C_r\frac{s^2}{(n)_m}(1+s^2/n)^{2r}\exp(-c'_r s^2/n),
\qquad (n)_m=n(n-1)\cdots(n-m+1).
```
The sum over $s\ge K\sqrt n$ is $o_K(1)n^{-r}$, where the coefficient tends to zero as $K\to\infty$. After an absolute rescaling of $K$ it therefore suffices to consider both corner squares of side $K\sqrt n$.

For fixed $K$, their populations are at most $C_{K,r}\log n$ except with probability $O_{K,r}(n^{-r-2})$. When $A\ge m+1$, choose $m+1$ points with both spans $O_{K,r}(\log n)$. There are $O_{K,r}(n(\log n)^{2m})$ prescriptions, counting coordinate minima and the other offsets. Their expected count is $O_{K,r}((\log n)^{2m}/n^m)=o(n^{-r})$. Thus only the consecutive decreasing block contributes to the limit.

## Counting blocks

In one fixed corner condition on the block starting at position $p$ with least value $v$. Deletion and standardization give a uniform permutation of size $n-m$ with minimum degree $d'$. Write $c=p+v-2$. If $d'\ge c+r$, there is no further southwest vertex: it would have standardized coordinates at most $p-1,v-1$, hence degree at most $p+v-4$. The northeast side is occupied for all sufficiently large $n$ in the fixed corner. The crossing set then has size $c$ and all its members meet every block vertex. Degrees of the remaining vertices can only increase on reinsertion. Consequently the block witnesses the cut and $d=c+r$. Conversely, if the block witnesses this cut with $A=m$ and $c\le d-r$, its degree calculation gives $d=c+r$, and deletion reduces any survivor’s degree by at most $m$. It follows that the conditional witness probability lies between $\Pr(d'\ge c+r)$ and $\Pr(d'\ge c-1)$.

The extra condition in the theorem is now exactly $c+r>x\sqrt n$. The two conditional probabilities converge uniformly in the fixed square to $e^{-(p+v)^2/n}$, up to $o_{K,r}(1)$, by the continuous degree limit. Each block has probability $1/(n)_m$. Two disjoint blocks in the compact squares have total pair probability $O_{K,r}(n^{-2r})$. If distinct compatible blocks overlap at row shift $1\le h\le r$, they form one longer decreasing block with $m+h$ prescribed entries. Their total probability is $O_{K,r}(n/(n)_{m+h})=O_{K,r}(n^{-r-h})$. Overlap in just the positions or just the values is impossible. Thus Bonferroni’s inequalities allow us to sum the single-block probabilities.

Multiplication by $n^r$ and summation of the two corner Riemann sums, followed by $K\to\infty$, now give
```math
2\int_{u,v\ge0,\ u+v>x}e^{-(u+v)^2}\,du\,dv
=2\int_x^\infty t e^{-t^2}\,dt=e^{-x^2}.
```
At $x=0$ the extra degree condition is automatic because $d-\kappa\ge r\ge1$.
