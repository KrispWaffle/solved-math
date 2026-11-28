# The exact boundary for forbidden induced paths

**Theorem.** For every fixed positive integer $k$, induced subgraph isomorphism on $P_k$-free bipartite permutation graphs is polynomial-time solvable for $k\le5$ and NP-complete for $k\ge6$. The hardness direction holds with a star forest as the pattern. Each connected component of the host has a vertex cover of size two.

The polynomial side is Proposition 3 of Alecu, Lozin and Malyshev. We prove the hardness side. The hereditary class at $k=6$ omits the linear forest $P_6$, so under $\mathrm P\ne\mathrm{NP}$ this disproves their Conjecture 2. The reduction itself is unconditional. [Original paper, §5](https://arxiv.org/pdf/2010.14467v1#page=18)

## Two centers and their leaves

Let a host component have two nonadjacent vertices $L,R$. Give $L$ exactly $a$ private neighbors, give $R$ exactly $b$ private neighbors, and let them have $c$ common neighbors. All these neighbors are independent. This is a blow-up of the path with five successive parts of sizes $a,1,c,1,b$. By a blow-up we mean replacing a path vertex by independent vertices and an edge by all edges between its two parts.

This component is a bipartite permutation graph. Label the path parts $U,L,W,R,V$ in path order. The two orders $L,U,R,W,V$ and $U,W,L,V,R$ disagree exactly on the edges of this path. Replace each part by its vertices in the same internal order in both lists. The resulting inversion graph has exactly the edges described above. Concatenate the two orders over different components in the same component order. Star forests have such representations as well, since each star is a blow-up of an edge. Each host component excludes even a six-vertex path as a subgraph. Such a path has three disjoint edges, and $L,R$ together meet every edge. A star forest also excludes $P_6$.

Fix a positive integer $H$ larger than $a,b$ and at least three, and set $c=H+\min(a,b)$. Put $s=a+b$. Three properties of this component govern the construction.

1. The maximum degree is $H+s$. The two center degrees are $a+c$ and $b+c$, and every other vertex has degree at most two. Consequently a star on $H+q$ leaves fits if and only if $q\le s$. The neighborhood of either center is independent, so this is an induced embedding.
2. If a star with $H+q$ leaves fits for $q\ge1$, it uses at least one common neighbor, since each private supply is less than $H$. Another star with at least three leaves would need the other center, which is adjacent to that common neighbor. They cannot be distinct components of an induced star forest in this bin.
3. Two stars, each with at least three leaves, must use the two different centers. Their leaves must all be private, since every common neighbor sees both centers. Their two demands are at most $a,b$ in one of the two orders. Every such pair can be placed using just its private leaves. At most two stars with at least three leaves can occupy the component.

## Turning a matching instance into a star forest

Numerical matching with target sums has two sets of $m$ labeled items with positive weights $x_i$ and $y_j$, and a positive target list $z_1,\ldots,z_m$. Every target needs one item from each set summing to its weight, using each item once. The problem is strongly NP-complete, so we take the weights in unary. [Garey and Johnson, SP17](https://perso.limos.fr/~palafour/PAPERS/PDF/Garey-Johnson79.pdf)

For each target value $w$, write $m_w$ for its multiplicity. Form one candidate for each pair of labels $(i,j)$ for which $w=x_i+y_j$ is a target value. Write $B_w$ for the number of these pairs of weight $w$ and $B=\sum_w B_w$. If $\sum_i x_i+\sum_j y_j\ne\sum_h z_h$ or some $B_w<m_w$, the instance is negative. Output the fixed negative instance asking for $K_{1,3}$ in $P_5$. An empty instance maps to the pair of empty graphs.

For the nonempty instance take $H=1+\max(\{3\}\cup\{3x_i\}_i\cup\{3y_j+1\}_j)$. For every candidate pair put one component of the preceding construction in the host, with
```math
a=3x_i,\quad b=3y_j+1,\quad s=a+b=3w+1,
\qquad c=H+\min(a,b).
```
The pattern has one ordinary star for each item, with $3x_i$ or $3y_j+1$ leaves, and $B_w-m_w$ additional stars of $H+3w+1$ leaves for each target value $w$. Call these additional stars blockers. All ordinary stars have at least three leaves.

Given a numerical matching, use the corresponding candidate bin for the two ordinary stars of each matched pair. Exactly $B_w-m_w$ bins of weight $w$ remain; each can host one blocker of that weight. Bins are distinct components, so this is an induced embedding.

Conversely, a blocker occupies its bin alone by property 2. The $B-m$ blockers leave precisely $m$ bins for $2m$ ordinary stars. By property 3 these bins each receive two. In every bin the adjusted number of leaves assigned is at most its capacity $s$. Count ordinary leaves directly and subtract $H$ from the number of leaves on a blocker. The total adjusted demand is
```math
\sum_i 3x_i+\sum_j (3y_j+1)+\sum_w(B_w-m_w)(3w+1)
=\sum_w B_w(3w+1),
```
the total capacity. Thus every bin attains equality. In each bin with two ordinary stars, both private supplies must be used exactly. Their residues modulo three force an item from the first set into the $a$ side and an item from the second set into the $b$ side. The original weights of this pair sum to the bin weight $w$. This argument also applies to repeated weights because the pattern still has a separate star for every item.

Every blocker attains equality too, so it occupies a bin of its own weight. Exactly $m_w$ two-star bins of each weight $w$ remain. They supply a numerical matching for the given target list.

## Complexity and scope

There are at most $m^2$ bins. Each has $2+a+b+c$ vertices and $a+b+2c$ edges. The pattern has $2m$ ordinary stars and at most $m^2$ blockers, all with polynomially many leaves in the unary input length. Constructing the two graphs as ordinary uncolored graphs takes polynomial time. Checking an induced embedding checks a proposed injection and all vertex pairs, proving membership in NP on the promised class. For the associated language that also checks the promise, bipartitions and pairs of permutation orders have polynomial certificates. For fixed $k$ one can test every ordered $k$-tuple for an induced $P_k$.

The constructed graphs exclude $P_6$ and therefore every longer induced path. For $k\le5$, the promised host is bipartite and $P_5$-free. An arbitrary pattern can first be checked for these same two necessary conditions by a bipartition test and inspection of all five-tuples. If it passes, the source algorithm applies to the pair. This proves both sides for every $k$. The conjecture about a unique hereditary source of hardness is false. Identifying every minimal hard subclass is a further classification question.

## A classification for classes closed under disjoint union and twin duplication

Let $\mathcal C$ be any hereditary class of bipartite graphs closed under disjoint union and under duplicating a vertex as an independent twin with exactly its neighbors. If $P_5\in\mathcal C$, these two operations give every host used in the reduction. Heredity supplies an edge from $P_5$, duplicating one endpoint gives each pattern star, and disjoint unions give the full pattern. The restricted induced subgraph isomorphism problem is therefore NP-hard. Only the host is promised to belong to the class in the source definition. Both graphs in this hardness construction belong to it. If $P_5\notin\mathcal C$, every host is bipartite and $P_5$-free by heredity. Reject a pattern violating either property, and apply Proposition 3 to every remaining pair. This describes the boundary for all classes with the stated closures, including those outside the permutation graphs. [Polynomial algorithm](https://doi.org/10.1002/jgt.23011)
