# No universal cutoff for prescribed permutation packings

Can the first five packing counts determine the entire sequence for every consecutive permutation pattern? Blitvić, Kammoun, and Steingrímsson asked this after comparing enumerations for patterns of length at most twelve. We construct pairs of the same length and overlap that first differ as late as desired. [Part I, §7, item 8](https://arxiv.org/html/2610.29846v1#S7)

## The patterns

For a pattern $p$ of length $K$ and overlap $m$, let $N_{p,m}(j)$ count the permutations of length $K+(j-1)(K-m)$ whose $j$ consecutive windows starting at $1+t(K-m)$, $0\le t<j$, have relative order $p$. Other occurrences are allowed. Equivalently, regard the positions as elements of a poset and impose the rank order of $p$ in each prescribed window. Giving ranks $1,2,\ldots$ to the positions in a linear extension gives exactly one packing and conversely. [Definitions 2.5–2.6, Remark 2.7, and Theorem 5.3](https://arxiv.org/html/2610.29846v1)

Fix $k\ge2$. Form two patterns $p_k,q_k$ by concatenating the following four-entry columns, in order from $i=1$ through $k$:

$$
\begin{aligned}
p_k(i)&=(i,\ k+i,\ 2k+i,\ 4k+1-i),\\
q_k(i)&=(i,\ k+i,\ 3k+1-i,\ 4k+1-i).
\end{aligned}
$$

In both cases set $K=4k$ and $m=4k-4$. Each of the four rows uses a different interval of $k$ ranks, so both words are permutations. Each window advances by one column. Removing its first or its last column gives the same relative order, so the overlap is admissible. Write $C_j=\binom{2j}{j}/(j+1)$ for the Catalan numbers.

**Theorem.** For every $j\ge1$, $N_{q_k,m}(j)=C_j^2$. For $1\le j\le k$, $N_{p_k,m}(j)=C_j^2$, while

$$
N_{p_k,m}(k+1)=C_{k+1}^2+C_k^2.
$$

Thus there is no universal cutoff. Even if the patterns must have the same length and overlap, any cutoff valid for length $4k$ must be at least $k+1$. The existence of some finite length-dependent bound follows already from the finiteness of the set of patterns and overlaps of fixed length. The theorem gives a lower bound on its growth.

## A pair of increasing rows

Write $L=k+j-1$ for the number of columns in a packing. Denote positions in two adjacent rows by $X_1,\ldots,X_L$ and $Y_1,\ldots,Y_L$. Suppose both rows increase from left to right and each window puts its $X$ entries below its $Y$ entries. The window inequalities on these rows are equivalent to the two increasing chains and

$$
X_{t+k-1}<Y_t\qquad(1\le t\le j).
$$

Indeed, these compare the largest $X$ and the smallest $Y$ in each window. Consecutive entries within a row share a window since $k\ge2$. In a linear extension restricted to these rows, the first $k-1$ copies of $X$ form a forced prefix, and the last $k-1$ copies of $Y$ a forced suffix. The remaining $j$ copies of each letter interleave as a Dyck word, since the $t$-th remaining $X$ must precede the $t$-th $Y$. The ballot count is $C_j$. Reversing column order gives the same count for two decreasing rows.

For both patterns label the four rows $A,B,C,D$ in order of their value ranges. Within a window it suffices to impose the comparisons on adjacent rows, since the others follow by transitivity.

## The pattern with independent pairs

In $q_k$, rows $A,B$ increase and rows $C,D$ decrease. The last window gives $B_L<C_L$. These are respectively the largest $B$ and the smallest $C$. Every $A$ is below some $B$, and every $D$ above some $C$, by its own window. Consequently a full extension is exactly a two-row extension on $A,B$ followed by one on $C,D$. Each can be chosen independently, giving $C_j^2$.

## When two interleavings can interact

In $p_k$ the first three rows increase and $D$ decreases. In the last window $C_L<D_L$, so every extension ends with the entire $D$ chain in its forced order. It remains to interleave $A,B,C$.

Restrict an extension to $A,B$ and to $B,C$. Each restriction has $C_j$ choices. Conversely, choose any two such restrictions. Align their common $B$ chain. In each gap between consecutive $B$ entries, including the two exterior gaps, shuffle its $A$ entries and $C$ entries, preserving the order of each. These shuffles produce exactly the extensions with the chosen restrictions. In particular there is no missing $A,C$ test. Every such comparison required by a window already follows through a $B$ in that window.

The two-row inequalities give $A_L<B_j$ and $B_k<C_1$. If $j\le k$, all $A$ entries must occur before $B_j$, and all $C$ entries after $B_k$. The two kinds of entries occupy disjoint gaps. There is exactly one full extension per pair of restrictions.

Take $j=k+1$, so $L=2k$. The only possible shared gap is between $B_k$ and $B_{k+1}$. Here $A_{2k-1}<B_k$, so only $A_{2k}$ can use it. Also $B_{k+1}<C_2$, so only $C_1$ can use it. If both use the gap there are exactly two orders. Every other pair of restrictions gives one order.

For the $A,B$ restriction to put $A_{2k}$ in that gap, its reduced Dyck word must end in $AB$. Its preceding $2k$ letters can be any Dyck word of semilength $k$. For the $B,C$ restriction to put $C_1$ there, its reduced word must start with $BC$, since $B_k$ is the first $B$ after deleting the forced prefix. Its remaining $2k$ letters are again arbitrary Dyck words. There are precisely $C_k^2$ pairs with a second extension, proving the stated formula. $\square$

For $k=5$ the patterns have length 20 and overlap 16. Their first five counts are $1,4,25,196,1764$. At the sixth occurrence the counts are $19188$ and $17424$. The construction above gives the first disagreement at every prescribed index $k+1\ge3$. [Exact checker](verify.py)
