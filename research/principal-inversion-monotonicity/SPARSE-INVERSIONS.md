# Inversion monotonicity in the sparse range

Write $a(n,k)$ for the number of permutations of length $n$ with $k$ inversions that avoid 1324. For every nonnegative integer function $K(n)=o(n^2/(\log n)^2)$, there is $N$ such that

```math
a(n+1,k)\ge a(n,k)\qquad(n\ge N,\;0\le k\le K(n)).
```

The inequality is strict throughout $2n-6\le k\le K(n)$. In particular, the result covers every fixed power $k\le n^{2-\varepsilon}$ for $\varepsilon>0$. The full conjecture includes inversion counts with positive quadratic density. Linusson and Verkama proved the assertion for $k\le2n-7$, and Meng proved growing strips above that line with width proportional to $\sqrt n$. [Original conjecture](https://arxiv.org/abs/1111.5736) · [Linusson–Verkama](https://arxiv.org/abs/2408.15075) · [Meng, §7.3](https://arxiv.org/html/2609.06717v2#S7.SS3)

## Removing small dominating sets

In an inversion graph, two positions are adjacent when their values occur in decreasing order. Its connected components are precisely the sum components of the permutation. A 1324-avoider has at most two nontrivial components. If there were three, an inverted pair in the middle component, with one point in each outer component, would give 1324.

In each nontrivial component a shortest path between the first and last positions dominates the component. Indeed, if a vertex were outside the path and adjacent to none of its vertices, the path vertices before it would have smaller values and those after it would have larger values. Both groups are nonempty, and no edge crosses between them. The path is induced, and the inversion graph of a 1324-avoider contains no induced six-vertex path. Thus at most five vertices per nontrivial component suffice. This remains true after arbitrary deletions by pattern avoidance. [Meng, Lemma 5.25](https://arxiv.org/pdf/2609.06717v2#page=25)

Let $\pi$ be a residual at length $n$ with $k$ inversions. It is indecomposable and has minimum inversion degree at least two. In one round, remove such a dominating path from each nontrivial component and keep all vertices of degree zero. Repeat until a degree-zero vertex survives. If one appears in round one, perform a second round, again keeping all isolated vertices. If the whole remaining graph was already edgeless, count that second round with zero removals. [Meng, Corollary 6.2](https://arxiv.org/html/2609.06717v2#S6.SS1)

After $r$ rounds, at most $10r$ vertices have been deleted. Every final survivor sends at least $r$ distinct inversions to deleted vertices. For $r\ge2$ with the first isolate appearing in the last round, domination supplies a distinct neighbor in each round. If the first isolate appeared in round one then $r=2$. The survivors already isolated after that round had at least two neighbors in the original residual, both deleted. Every other final survivor was dominated in each of the two rounds.

The process stops after $r=O(1+k/n)$ rounds in the range of the theorem. Otherwise put $r_0=\lceil2k/n\rceil+2$. Since $k=o(n^2)$, for large $n$ we have $10r_0<n/2$. If no isolate has appeared after $r_0$ rounds, each remaining point has supplied at least $r_0$ deleted inversions, giving $k\ge r_0(n-10r_0)>k$. There are therefore remaining vertices and a surviving isolate. For the final inversion count $u$ and $m=k-n$ we obtain, uniformly for large $n$,

```math
u\le k-r(n-10r),\qquad m-u\ge (r-1)n-10r^2\ge rn/4\qquad(r\ge2).
```

## Counting the remaining permutation

At an isolated position the surviving pattern splits as $\alpha\oplus1\oplus\beta$. The prefix $\alpha$ avoids 132 and the suffix $\beta$ avoids 213. Otherwise the isolate completes a forbidden pattern. At fixed length, a 132-avoider of inversion weight $v$ is encoded by a partition of $v$ inside the staircase. Its Lehmer digits $d_i$ count the later entries smaller than its $i$th entry. An ascent has nonincreasing digits unless a later value lies between the ascent values, which creates 132. More precisely a 132-avoider has weakly decreasing digits: adjacent descents strictly decrease the digit, and adjacent ascents have equal digits. Conversely a permutation with weakly decreasing digits avoids 132: a 132 occurrence contains an adjacent ascent crossing the last letter of that occurrence before this letter appears, producing a strict digit increase there. Digits $0\le d_i\le l-i$ uniquely give a permutation of length $l$. Reverse-complementation applies the same enumeration to 213. [Partition encoding in the original paper](https://arxiv.org/abs/1111.5736)

Let $p(v)$ count partitions and $p_2(v)=\sum_{j=0}^v p(j)p(v-j)$. The Hardy–Ramanujan estimate and Cauchy–Schwarz give
```math
\log p(v)=\pi\sqrt{2v/3}+O(\log(v+2)),\qquad
\log p_2(v)=h\sqrt v+O(\log(v+2)),\quad h=2\pi/\sqrt3 .
```
For the lower estimate on $p_2$, take the two parts of the weight as nearly equal as possible. [Hardy and Ramanujan, *Asymptotic formulae in combinatory analysis*](https://doi.org/10.1112/plms/s2-17.1.75)

For fixed $r$ and $u$, choose the number and positions of the deleted entries, their values and their matching in at most $(10r+1)n^{30r}$ ways. Mark the isolate in at most $n$ ways. The partition pair determines the remainder at the resulting fixed lengths, so at most that prefactor times $n p_2(u)$ residuals are encoded. The choices of $r$ and $u$ add polynomial factors. All logarithmic overhead at a given $r$ is $O(r\log n)$.

## Comparing with the injection complement

Prepending the maximum to an arbitrary length-$n$ avoider of weight $m=k-n$ gives a length-$(n+1)$ avoider of weight $k$ outside the Linusson–Verkama injection image. The count difference is that complement’s size minus the number of residuals. Thus $a(n,m)$ is a lower bound for the positive term. [Meng, equation (4), Lemma 3.1 and Theorem 5.35](https://arxiv.org/html/2609.06717v2#S5.SS7)

To lower-bound $a(n,m)$, take $\alpha\oplus\beta$ with fixed lengths $\lfloor n/2\rfloor,\lceil n/2\rceil$, where $\alpha$ avoids 132 and $\beta$ avoids 213. A crossing copy of 1324 would need a 132 in the first side or a 213 in the second, since the only proper sum cuts of 1324 are after its first and third entries. An internal copy is excluded by either side’s own restriction. Give the two sides inversion weights $v=\lfloor m/2\rfloor,\lceil m/2\rceil$.

For each side use partitions having at most $b=\lfloor n/5\rfloor$ rows and columns. They fit its staircase since $2b\le\lfloor n/2\rfloor$. Removing one part of size greater than $b$, or transposing first for the height, shows that at most $2(v+1)p(v-b)$ partitions are excluded, with zero excluded when $v\le b$. By the preceding estimate, the excluded fraction is at most $\exp(O(\log n)-c n/\sqrt k)$ for a fixed $c>0$ when $v>b$. It tends to zero uniformly because $\sqrt{K(n)}\log n=o(n)$. All pairs with these lengths and weights are distinct, giving
```math
\log a(n,m)\ge h\sqrt m-O(\log n).
```

For every attainable $u$ after $r$ rounds,
```math
\sqrt m-\sqrt u=\frac{m-u}{\sqrt m+\sqrt u}\ge\frac{rn}{8\sqrt k}.
```
This beats $O(r\log n)$ uniformly in $2n-6\le k\le K(n)$. After summing over the polynomially many possible $r,u$, the residual count is strictly smaller than $a(n,m)$. The complement comparison proves the claimed strict inequality. Linusson–Verkama covers the remaining values of $k$. The proof uses no enumeration of residuals and no assumption on the base-length conjecture.

## The stable count is already asymptotically correct

In the same range,
```math
a(n,k)=(1-o(1))p_2(k).
```
For the upper bound compare through every later length to the known plateau $p_2(k)$ at length at least $k+2$. The proof above is uniform there because $\log l/l$ decreases for $l\ge n\ge3$. For the lower bound take the two fixed-length direct-sum factors across every pair of weights adding to $k$. At most $4(k+1)p_2(k-b)$ pairs have a part or a column longer than $b=\lfloor n/5\rfloor$. This follows by removing a long part in either partition, after conjugation when needed. For $k\le b$ the error is zero. Otherwise its ratio to $p_2(k)$ is at most $\exp(O(\log n)-c n/\sqrt k)$ and tends to zero uniformly. [Stable inversion counts, Claesson–Jelínek–Steingrímsson](https://arxiv.org/abs/1111.5736)
