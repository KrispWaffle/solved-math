# A separator from a shared gap

Let $\pi$ be a permutation of length $K$, let $m$ be the overlap and set $d=K-m$. Start consecutive windows $d$ positions apart. Within each window impose the rank order of $\pi$ on its positions and take the transitive closure of all these comparisons. This is the paper’s packing poset $\mathcal P_\pi^m(j)$ for $j$ prescribed windows. [Part I, Definition 5.4](https://arxiv.org/html/2610.29846v1#S5)

**Theorem.** Suppose $2\le m\le K/2$. Write the first $m$ ranks of $\pi$ as $P_1,\ldots,P_m$ and the last $m$ ranks as $S_1,\ldots,S_m$, in position order. Assume

$$
1=P_1<\cdots<P_m<S_1<\cdots<S_m.
$$

If some $g<m$, with $g\ge1$, satisfies both $P_g+1<P_{g+1}$ and $S_g+1<S_{g+1}$, then the last position $z=K$ of the first window is a separator for every $j\ge3$.

Taking $m=2$, $P=(1,a)$ and $S=(b,c)$ proves the concrete assertion in §7, item 5. The theorem also allows $c=K$ and arbitrarily large overlaps. For example, for any $m\ge2$ take $K=2m+2$, omit $2$ from the prefix $1,\ldots,m+1$, omit $m+3$ from the suffix $m+2,\ldots,2m+2$, and put those two omitted ranks in the middle. The first boundary gap works for every $m$. [Original question](https://arxiv.org/html/2610.29846v1#S7)

## Comparability with every position

The first two windows both contain $z$. Each window is totally ordered by rank, so $z$ is comparable with all of their positions. In the second window $z$ has rank $P_m$. The minimum of the third window is shared with the second, where it has rank $S_1>P_m$. Each later minimum is likewise a suffix rank $S_1$ in the preceding window and lies strictly above that window’s minimum. It follows that every position from the third window onward lies strictly above $z$.

## Two positions that stay incomparable

At the join of two consecutive windows, the $g$th shared position has rank $S_g$ in the earlier window and $P_g$ in the later window. Choose the position of rank $S_g+1$ in the earlier window and the position of rank $P_g+1$ in the later window. They lie strictly between the same two shared positions. They are distinct because the first position has a rank absent from the suffix and therefore occurs before the later window begins.

To see why no chain can join these positions in either direction, give them equal integer heights in a function that increases strictly along every poset comparison. For this construction only, subtract one from all ranks and positions, and index the boundary lists from $0$ to $m-1$. For a rank $r$ define

$$
A(r)=\max\bigl(\{S_i:P_i\le r\}\cup\{0\}\bigr),\qquad
B(r)=\max\bigl(\{P_i:S_i\le r\}\cup\{0\}\bigr).
$$

Assign the within-window height

$$
h(r)=
\begin{cases}
r+A(r), & r<S_0,\\
2K+r+B(r), & r\ge S_0.
\end{cases}
$$

Both maxima are nondecreasing. Each branch of $h$ therefore increases strictly. The lower branch has height at most $2K-2$, and the upper one starts at or above $2K$. At a shared position, $A(P_i)=S_i$ and $B(S_i)=P_i$, so

$$
h(S_i)=2K+h(P_i).
$$

In window $t$, starting from $t=0$, give rank $r$ height $2Kt+h(r)$. The displayed identity makes this assignment agree on overlaps. Since $m\le d$, nonadjacent windows share no positions. Every generating comparison, and therefore every strict path in the poset, increases global height.

In an occupied gap the same equality holds one rank later. Neither list acquires a new boundary rank at its chosen successor, so $h(S_g+1)=2K+h(P_g+1)$. The two chosen positions have the same global height. They are incomparable in the whole stack, for every window count.

## The two sides of the separator

At the first join both chosen positions are below its $(g+1)$st shared position in the original one-based convention. That shared position is at or below $z$, the last shared position. At the second join both chosen positions exceed its $g$th shared position. The latter has rank $S_g>P_m$ in the second window, above $z$. This gives an incomparable pair on each side and completes the proof.

For example, take $\pi=13257846$ with overlap two. In three windows the separator is position $8$. Positions $4$ and $9$ form the incomparable pair below it, and positions $10$ and $15$ form a pair above it. The argument above applies to every admissible pattern and every $j\ge3$. [Lean proof](../../lean/SolvedMath/PatternSeparator.lean)
