# The sharp deletion gap

The unrestricted range question follows from the 1989 antichain inequality. This note preserves additional ways to derive the lower bound. [Prior-result finding](README.md#prior-result-finding-28-november-2026)

Let $P$ be a nonempty finite poset of size $n$ with a distinguished element $x$. Let $q$ count the elements comparable to $x$, including $x$ itself. The direct counting argument gives

```math
q\,e(P)\ \ge\ n\,e(P-x).
```

If $q=n$, every listing of $P-x$ leaves exactly one slot for $x$, giving $e(P)=e(P-x)$. Otherwise $n\ge2$, $q\le n-1$, and $\rho(P,x)\ge n/(n-1)$. These alternatives hold for arbitrary distinguished elements.

## A direct injection

Insert $x$ at any of the $n$ positions of any extension of $P-x$, temporarily ignoring the relations involving $x$. In the resulting word mark the $q$ positions occupied by elements comparable to $x$, including the position of $x$. Record the index of $x$ among the marked positions. Keeping the marked positions themselves fixed, move $x$ within their subsequence until every predecessor precedes it and every successor follows it. All the other marked letters retain their mutual order. This specifies a unique rearrangement since every predecessor of $x$ precedes every successor in the original extension of $P-x$.

The new word is an extension of $P$. Any predecessor that moves goes earlier, and any successor that moves goes later. A letter incomparable to $x$ can have no relation requiring it to precede a predecessor or to follow a successor. Thus moving these marked letters past unmarked ones preserves all required comparisons. To invert on the image, find the marked positions from their letters and restore $x$ to its recorded index in that subsequence. The new word and one of $q$ indices recover the original word, and hence its deleted extension and insertion slot. This injects $n\,e(P-x)$ choices into $q\,e(P)$ choices.

## Counting the insertion slots

Write $D$ for the strict predecessors of $x$, $U$ for its strict successors, and $I$ for the remaining elements of $P-x$. In a listing of $P-x$, restrict separately to $D\cup U$ and to $I$. Fix the two resulting orders. All elements of $D$ precede all elements of $U$ by transitivity. There are $q$ gaps in the first listing, including its two ends. The central gap, indexed $d=|D|$ starting from zero, separates $D$ from $U$.

All extensions giving this pair of orders correspond bijectively to feasible allocations of the $|I|$ elements among the gaps. Their order within and across gaps is the fixed order on $I$. For each individual $y\in I$, every lower constraint from the first listing comes from $D$, and every upper constraint comes from $U$. Indeed, $u<y$ with $u\in U$ or $y<v$ with $v\in D$ would make $x,y$ comparable. Consequently the allowed gap indices for $y$ form an interval containing $d$.

Write $b_j$ for the number of elements in gap $j$. If $b_j>0$, moving one unit of occupancy from $j$ to $d$ preserves feasibility. For $j<d$, remove one copy of $j$ from the sorted list of gap indices and insert one copy of $d$. Every changed index shifts weakly rightward toward $d$. The case $j>d$ shifts weakly leftward toward $d$. In both cases each individual index stays in its allowed interval and the list stays sorted.

Fix all occupancies outside $j,d$ for some $j\ne d$, and write $M=b_j+b_d$. In each nonempty class the feasible values of $b_j$ are $0,\ldots,s$ for some $s\le M$. Each corresponds to exactly one extension with the two prescribed orders. Their mean is $s/2$, while the mean of $b_d$ is $M-s/2\ge s/2$. Sum this inequality over the classes and over the possible pairs of restricted orders. For a uniform extension of $P-x$, it gives $\mathbb E b_d\ge\mathbb E b_j$ for every $j$. Since $\sum_j b_j=n-q$, we have $q\,\mathbb E b_d\ge n-q$.

Each listing of $P-x$ extends to $P$ in exactly $1+b_d$ ways, and deleting $x$ recovers that listing. Thus $e(P)/e(P-x)=1+\mathbb E b_d\ge n/q$.

## Consequence for the unrestricted size question

If $d>c\ge1$ and a poset with $n$ elements has ratio $d/c$, then

```math
n\ge 1+\frac{c}{d-c}.
```

For every $c\ge1$, take a chain of length $c$ and one further element incomparable to every member of the chain. Distinguish any member of the chain. The extra element can be placed in any of $c+1$ slots, and in any of $c$ slots after the distinguished member is removed. The lower bound and this construction give $\nu(c,c+1)=c+1$. More generally, a chain of length $q$ disjoint from any poset on $n-q$ elements attains $e(P)/e(P-x)=n/q$ for $x$ in the chain, by shuffling the components.

Along $d=c+1$, the proposed unrestricted upper bound grows as $O(\log c\log\log c)$ whereas $\nu(c,c+1)$ grows linearly. This answers the question of dropping the hypothesis in the negative. The fixed-gap upper bound and the conjectural error term with the original restriction have different scopes. [Chan and Pak, discussion after Theorem 1.8](https://arxiv.org/pdf/2401.09723v2) · [Ghodsi, §7](https://arxiv.org/html/2607.10084v1#S7)

## A geometric derivation of the inequality

The chain polytope of $P$ consists of nonnegative vectors whose coordinate sum on every chain is at most one. Its volume is $e(P)/n!$. Start with any point in the chain polytope of $P-x$. For $0<s<1$, keep the coordinates in $I$, multiply the other $q-1$ coordinates by $1-s$, and assign $s$ to $x$. Every chain through $x$ uses only scaled coordinates and $x$. Every other chain has weakly decreased coordinate sum. This injective linear change on the remaining coordinates has determinant $(1-s)^{q-1}$. Thus the slice of the chain polytope at $x=s$ has volume at least $(1-s)^{q-1}e(P-x)/(n-1)!$. Integration from zero to one gives the same bound. [Stanley, Two poset polytopes, Corollary 4.2](https://doi.org/10.1007/BF02187680)
