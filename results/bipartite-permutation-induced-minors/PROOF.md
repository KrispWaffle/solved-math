# An induced-minor antichain of bipartite permutation graphs

**Theorem.** Finite bipartite permutation graphs are not well-quasi-ordered by induced minors. There is an explicit infinite antichain of graphs of maximum degree five and bandwidth at most four. This answers Open Problem 2 of Alecu, Lozin and Malyshev and gives a negative answer to the bipartite-permutation part of the question attributed to Lozin and Mayhill. [Journal §3](https://doi.org/10.1002/jgt.23011) · [Lozin and Mayhill](https://doi.org/10.1007/s11083-010-9188-7)

## Path blowups

For a sequence of positive integers, make one independent set of the indicated size for each position, called a row. Join every vertex in a row to every vertex in the next row, and add no other edges. Every such graph is a bipartite permutation graph. Color by row parity. To obtain two permutation orders, first order rows by $2i+3$ for even $i$ and $2i$ for odd $i$. In the second order use $2i$ for even $i$ and $2i+3$ for odd $i$. Only consecutive row pairs switch order. Replace each row by its vertices in the same internal order on both lines. Exactly the edges of the graph appear as inversions.

An induced-minor model of $H$ in $G$ assigns each vertex of $H$ a disjoint nonempty connected set of vertices of $G$. For distinct vertices of $H$ the two sets have an edge between them exactly when those vertices are adjacent. The sets are the vertices merged by edge contractions after unused vertices are deleted. This description allows all intermediate graphs in the induced-minor relation. [Branch-set characterization](https://arxiv.org/abs/1510.07135)

## Common neighbors force the row

Suppose the host is a path blowup with at most $M$ vertices in every row. The support of a connected branch set, meaning the set of rows that it meets, is an integer interval. An edge can only move one row.

Take two nonadjacent target vertices $u,v$. Their branch sets are anticomplete. If both meet the same row $t$, neither branch can leave that row: its first step out would give an edge to the other branch in row $t$. A connected set contained in an independent row is a singleton. Otherwise the two support intervals are separated. Between the rightmost row $b$ of the left support and the leftmost row $c$ of the right support we have $c\ge b+2$, since adjacent rows are complete to one another. Every branch adjacent to both supports meets row $b+1$. It must reach a row at most $b+1$ and one at least $c-1$, and its support is an interval. Disjointness gives at most $M$ such branches. Thus if $u$ and $v$ have more than $M$ common neighbors, their branches must be singleton vertices in the same row.

## Which blowups contain which induced minors?

Fix $s\ge2$ and an integer $M<2s$. Give every graph two outside rows of size $s$ and at least two internal rows, all of whose sizes belong to $[s,M]$. For two graphs in this family, the following conditions are equivalent.

1. The first graph is an induced minor of the second.
2. The first graph is an induced subgraph of the second.
3. Its sequence of internal row sizes, in either order, fits coordinate by coordinate beneath a consecutive block of the second graph’s internal row sizes.

In the first graph, two vertices of an internal row have at least $2s>M$ common neighbors in the two adjacent rows. In any model the entire internal row therefore uses singleton vertices in one host row. Different internal rows must use different host rows, since two groups of at least $s$ disjoint vertices cannot fit together. Neighboring internal rows have edges, so their host rows are consecutive. An injective unit-step walk on the line is monotone. The target internal rows thus occupy consecutive host rows in forward or reverse order, respecting their sizes.

The first occupied internal row in target order has a free host row available on its outside. If it were at the host boundary, every one of the $s$ target endpoint branches would have to touch its only neighboring host row to be adjacent to this occupied row. That neighboring host row already represents the second internal row with at least $s$ vertices. This would require at least $2s$ vertices there. The same argument applies at the opposite end. The occupied block is therefore internal to the host. This proves the third condition. Conversely, choose the required numbers of vertices from the block and $s$ vertices from each immediately adjacent outside row. The induced graph is exactly the target. Every induced subgraph is also an induced minor.

## The antichain

For $n\ge2$, take the row sizes
```math
(2,3,\underbrace{2,\ldots,2}_{n\ \mathrm{rows}},3,2).
```
The two internal rows of size three must occupy the only two such rows of the host. The number of intervening rows is consequently preserved. Two members are comparable exactly when their parameters are equal. The longest edge in the consecutive row ordering spans at most four positions, since neighboring row sizes sum to at most five. Each vertex has at most five neighbors, since no two triple rows are distance two apart. The construction answers the question for the entire class by giving an infinite sequence with no comparable pair. The separate question about ordinary unit interval graphs remains outside this conclusion.

Earlier planar nested-lozenge antichains also have a central path of two-vertex rows, with pendant leaves marking the ends. Their pendant supports give an asteroidal triple, which prevents a permutation representation. Here, changing the two internal row sizes marks the ends while keeping a permutation representation. The common-neighbor argument establishes the full containment criterion for bounded-width blowups. [Błasiok, Kamiński, Raymond and Trunck, §4 and Figure 6](https://arxiv.org/pdf/1510.07135#page=11)
