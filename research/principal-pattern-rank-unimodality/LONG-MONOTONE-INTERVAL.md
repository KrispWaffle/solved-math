# Principal ideals of hosts with a long monotone interval

Suppose a permutation of length $n$ has an interval of $M\ge1$ consecutive positions with consecutive values in increasing or decreasing order. Let $s=n-M$ count the outside entries. The numbers $D_m$ of distinct patterns satisfy
```math
D_0\le\cdots\le D_M,\qquad
D_{s+1}\ge D_{s+2}\ge\cdots\ge D_n .
```
Consequently every host with a monotone interval containing **at least $\lfloor n/2\rfloor$ entries** satisfies Vatter’s principal-downset conjecture. If $s+1<M$, all ranks from $s+1$ to $M$ have the same size. These inequalities apply to arbitrary arrangements of the entries outside the interval. They follow from the existing first-half theorem and the common-position reconstruction used by Kaiser and Klazar. [Vatter's conjecture](https://arxiv.org/pdf/2602.16355v4#page=4) · [Kaiser–Klazar, Lemma 4.1](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/EJC/Volume_9/PDF/v9i2r10.pdf#page=14)

## Increasing ranks

Extend the interval from $M$ to $M'$ by replacing it with a longer monotone permutation in the same orientation at the same position in the permutation obtained by contracting the interval to one entry. The sets of patterns at each length at most $M$ are identical in the two hosts. An embedding uses some outside entries and $r\le M$ entries in the interval. Any choice of $r$ entries there has the same comparisons to all retained outside entries and gives the same internal order. This works in both directions. Taking $M'$ sufficiently large puts every level through $M$ in the increasing half of the enlarged host, by Pouzet and Rosenberg's theorem. The same levels of the original host are therefore nondecreasing. [First-half theorem](https://www.sciencedirect.com/science/article/pii/S0195669886800075)

## A common pair of positions in every long pattern

Let $u$ positions precede the interval in the host and $v$ follow it, so $u+v=s$. In every embedding of a pattern of length $m+1$, at most $u$ chosen entries precede the interval, and at most $v$ follow it. Therefore all pattern positions in the fixed window $[u+1,m+1-v]$ come from the interval. When $m\ge s+1$ the window contains the two positions $j=u+1$ and $j+1$. Their pattern values are consecutive in the specified orientation: no chosen host point between their values can lie outside the interval since its values were consecutive, or inside it since the chosen entries at $j,j+1$ are consecutive in the monotone subsequence.

Delete pattern position $j$ and standardize. This maps into the length-$m$ patterns of the same host. Its inverse on the image duplicates the entry now at position $j$ into a two-entry increasing or decreasing interval in the known orientation. The new point occupies the first position of the pair. This reconstructs the original pattern uniquely and proves $D_{m+1}\le D_m$. Kaiser and Klazar use this common-position reconstruction when at least two entries remain in the interval after deletion. Here the orientation is fixed by the host, so one remaining entry suffices. Homberger’s run lemma also identifies the equality of patterns obtained by deleting different entries of a run. [Kaiser and Klazar](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/EJC/Volume_9/PDF/v9i2r10.pdf#page=14) · [Homberger, Lemma 5](https://arxiv.org/abs/1211.7117)

If $M\ge s$, the increasing comparisons for $m<M$ and the decreasing comparisons for $m\ge s+1$ leave at most one comparison undetermined. Either sign of that comparison yields a unimodal sequence. In the overlap the inequalities force equality.

When $n=2s-1$ and $M=s-1$, the exact first-half theorem gives $D_{s-1}\le D_s$ as well: in general $D_j\le D_{j+1}$ whenever $2j+1\le n$. The only undetermined comparison is again between $D_s$ and $D_{s+1}$. This proves the stated floor convention. The tail threshold $s+1$ cannot be lowered for all hosts: for the skew sum of two increasing blocks of lengths $M\ge s+1$ and $s\ge1$, one has $D_s=s$ and $D_{s+1}=s+1$. At length $k=s,s+1$ one counts the increasing pattern and a distinct pattern for each feasible way to take positive lengths from both blocks. [Pouzet, Theorem 5](https://arxiv.org/pdf/math/0703211#page=4)

## Exact stabilization of the rank sequence

Fix the outside entries and the location and orientation of the interval. Write $D_m(M)$ for the rank size with interval length $M$. The same fixed-position map gives the exact diagonal identity
```math
D_{m+1}(M+1)=D_m(M)\qquad(s+1\le m\le M+s).
```
Deleting the entry at $j$ from a length-$(m+1)$ embedding in the longer host leaves at most $M$ interval entries, so the resulting pattern occurs in the shorter host. Conversely, in every $m$-pattern of the shorter host, the window $[u+1,m-v]$ contains $j$. Duplicating its entry inserts one more interval element, hence gives a pattern in the longer host. The two operations undo each other. At intervals of size $M\ge s+1$, therefore, the full rank vector equals the vector at size $s+1$ with $M-s-1$ extra copies of its rank-$s+1$ value inserted at that rank: the levels through $s+1$ are stable by inflation, and all higher levels translate by the identity. This determines the plateau and both tails for the entire family of inflations.
