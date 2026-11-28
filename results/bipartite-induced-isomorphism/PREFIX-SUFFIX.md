# A hereditary hard class excluding a path

**Theorem.** Induced subgraph isomorphism is NP-complete on the class of bipartite permutation graphs with no induced eight-vertex path. The pattern in the reduction is a disjoint union of balanced complete bipartite graphs.

This disproves Alecu, Lozin and Malyshev’s proposed characterization under its stated hypothesis $\mathrm P\ne\mathrm{NP}$. The class in the theorem is hereditary and omits $P_8$, itself a linear forest. The reduction proving NP-hardness is unconditional. [Conjecture 2](https://arxiv.org/pdf/2010.14467v1#page=18)

## A graph with an adjustable split

For $t\ge1$, put $t$ columns $1,\ldots,t$ on one shore of a bipartite graph $B_t$. For each $j=1,\ldots,t$, put $t$ copies of a prefix row and $t$ copies of a suffix row on the other shore. The prefix row at $j$ sees exactly columns $1,\ldots,j$. The suffix row at $j$ sees exactly columns $j,\ldots,t$. A row of full length connects all columns, and every row has a neighbor, so $B_t$ is connected.

To realize $B_t$ as a permutation graph, order the rows by listing all prefix rows in increasing $j$, then all suffix rows in increasing $j$, breaking ties by copy number. The left and right endpoints of their column intervals are each nondecreasing. Form two linear orders, both with columns in their natural order. In the first, insert each row immediately before its left endpoint. In the second, insert it immediately after its right endpoint. Resolve ties by the row order. Two rows have the same relative order in both lists, as do two columns. A row and a column have opposite relative orders precisely when the column lies in the row’s interval. These two orders exhibit exactly the desired inversion graph. Concatenating the orders of different components realizes their disjoint union.

An induced matching in $B_t$ has at most two edges. Among three matched rows, two would be of the same type. Their neighborhoods are nested, so the endpoint of the smaller row’s edge is adjacent to the larger row as well. The path $P_8$ contains an induced matching given by edges $12,45,78$. Hence $B_t$ is $P_8$-free. A path is connected, so disjoint unions of the bins retain this property. Complete bipartite graphs also have permutation representations by two orders, with the order of the shores exchanged and the order within each shore preserved. Their induced paths have at most three vertices.

## The packing equivalence

A connected pattern component $K_{a,a}$ with $a\ge1$ lies in one host component. Under any embedding it uses exactly $a$ columns there. Indeed the image of an edge uses both shores, and every other vertex’s shore is then determined by its adjacency to the opposite side of this biclique. Swapping the shores still gives $a$ columns. Three distinct components with edges cannot occupy the same bin, since one edge from each would form an induced matching.

For $a,b\ge1$, two components $K_{a,a}$ and $K_{b,b}$ can be placed together in $B_t$ exactly when $a+b\le t$. Necessity counts their distinct columns. For sufficiency use the first $a$ columns and $a$ copies of the prefix row at $a$, then the last $b$ columns and $b$ copies of the suffix row at $t-b+1$. Each chosen row sees all its own chosen columns and none of the other piece’s columns. This gives an induced embedding, including when $a+b=t$.

## Reduction from numerical matching with target sums

In numerical matching with target sums there are $m$ items of weights $x_i$ in one set, $m$ items of weights $y_j$ in another, and $m$ targets $z_h$, all positive integers. The question is whether each target can be assigned one item of each type with sum exactly its target, using every item once. This problem is NP-complete even with unary weights. [Garey and Johnson, SP17](https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf)

If the total item weight differs from the sum of the targets, output the fixed negative test asking for an edge in a single isolated vertex. Otherwise form an uncolored pattern with one $K_{a,a}$ for each size $a=3x_i$ and each size $a=3y_j+1$. Form the host as the disjoint union of bins $B_{3z_h+1}$.

A numerical matching packs the pattern into the host by the two-component construction. Conversely, suppose there is an induced embedding. The $2m$ pattern components are distributed among $m$ bins holding at most two each, so every bin holds two. The sum of the pattern sizes is equal to the sum of the bin capacities as follows.

```math
\sum_i 3x_i+\sum_j(3y_j+1)=\sum_h(3z_h+1).
```

The column bound in each bin must therefore be an equality. Its capacity is one modulo three. The two assigned sizes have residues zero or one, so exactly one has each residue. Removing the residue and dividing by three recovers one $x_i$ and one $y_j$ with $x_i+y_j=z_h$. This holds for every bin, giving the required numerical matching.

The host $B_t$ has $t+2t^2$ vertices and $t^2(t+1)$ edges. Constructing all vertices and edges explicitly takes polynomial time in the unary input length. The pattern has $2a$ vertices and $a^2$ edges for each size $a$, also polynomial. An induced embedding has a polynomial certificate consisting of its vertex map, with injectivity and every adjacency and nonadjacency checked directly. This proves NP-completeness on the promised class. If inputs outside the class are to be rejected, bipartite permutation representations can be given by the two orders and checked against the graph, and all ordered eight-tuples can be tested for an induced path in polynomial time.
