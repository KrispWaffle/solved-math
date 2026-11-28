# Eventual affinity of diagonal differences

Fix any finite collection $B$ of classical patterns. Write $a(n,k)$ for the number of length-$n$ permutations with $k$ inversions avoiding 1324 and every member of $B$. For each integer $d$ define

```math
F_d(n)=a(n+1,n+d)-a(n,n+d).
```

**Theorem.** There are integers $s_d,t_d$ and a threshold $N_d$ such that $F_d(n)=s_d n+t_d$ for all $n\ge N_d$. Hence the further difference $F_d(n+1)-F_d(n)$ eventually equals $s_d$ on every diagonal. The class has a secondary limit sequence exactly when $s_d=0$ for every $d$. The theorem gives the existence of stabilization by the tertiary level for every pair in Problem 8.4, and for all finite additional bases. The source also predicts which pairs stabilize one level earlier. [Definitions and observations, §5.2](https://arxiv.org/html/2604.01143v2#S5.SS2) · [Problem 8.4](https://arxiv.org/html/2604.01143v2#S8)

An increasing interval is a consecutive block of positions occupied by consecutive values in increasing order. Inflating a point by such an interval means substituting an increasing permutation for that point, leaving all comparisons with other points unchanged. The proof reduces the large permutations that contribute to a finite list of descriptions with at most two variable interval lengths.

## Indecomposable end components

A component is a nonempty indecomposable factor in the unique direct-sum decomposition. For a component $w$, set $e(w)=\operatorname{inv}(w)-|w|+1$. This excess is nonnegative. Indeed, the inversion graph of a direct-indecomposable permutation is connected and therefore has at least $|w|-1$ edges. To see the connectivity assertion, the positions between the endpoints of any inversion edge belong to its connected component: each is adjacent to at least one endpoint. Thus the graph components are position intervals, and no inversion crosses their boundaries. These are exactly the direct-sum components.

**One-variable lemma.** For each fixed excess $e$, indecomposable 132-avoiders have a disjoint description by finitely many individual permutations and finitely many families with one variable increasing interval. The same is true for indecomposable 213-avoiders.

For a nonsingleton indecomposable 132-avoider, the maximum has $l$ entries to the left and $j\ge1$ on the right. Every left entry exceeds every right entry by 132-avoidance. Write the permutation uniquely as $(\alpha\oplus1)\ominus\beta$, where $|\alpha|=l$ and $|\beta|=j$. Counting inversions gives

```math
e=\operatorname{inv}(\alpha)+\operatorname{inv}(\beta)+l(j-1).
```

When $l>0$ and $j>1$, both are bounded and $|w|\le2e+2$. Otherwise $l=0$ or $j=1$. In either case the remaining arbitrary 132-avoider has exactly $e$ inversions. Any 132-avoider of fixed inversion count is $\gamma\oplus\mathrm{id}_t$, where $\gamma$ is its unique nontrivial first component, or the empty word for an identity. Indeed an inversion in any later component combines with an earlier point to form 132. The core $\gamma$ has length at most $e+1$. Consequently the two large forms are $1\ominus(\gamma\oplus\mathrm{id}_t)$ and $(\gamma\oplus\mathrm{id}_{t+1})\ominus1$. Restricting to lengths exceeding $2e+2$ makes the two cases disjoint. Each core and type gives a single family with a lower bound on its variable length. The remaining lengths give a finite list. Reverse-complement takes 132 to 213, preserves inversions and direct indecomposability, and takes an increasing interval to an increasing interval. This proves the lemma.

## Counting with two interval lengths

In a fixed permutation with up to two distinguished points inflated by increasing intervals, whether a pattern of length at most $h$ occurs depends only on the two lengths truncated at $h$. An occurrence can use at most $h$ entries of either interval. Any choice within an interval has the same comparisons with the rest of the permutation. A zero length, when allowed, means deletion of that point.

We will also test whether deleting a prescribed boundary entry makes the permutation decomposable. The four boundary entries mean the first position, last position, least value, and greatest value. This test depends only on the lengths truncated at three. After distinguishing lengths zero, one, and at least two, the boundary point belongs to the same block. Deleting it shortens that block by one, or removes the corresponding singleton. In a remaining template of length at least two, inflating a point by a nonempty increasing interval preserves decomposability in both directions. Existing cuts lift. A cut inside an inflated block implies that all earlier blocks lie below it and all later blocks above it, so that the base point is a singleton sum component and the base also has a cut. For a remaining template of just one point one must distinguish a singleton from a longer interval; truncating at three before deletion suffices. The empty permutation causes no ambiguity.

Split each variable into its finitely many lengths below the largest relevant threshold and its one infinite range above it. All these tests are constant on each resulting rectangle of lengths. The count at total length $n$ is eventually affine on each rectangle. With no free length the count eventually vanishes. With one free length there is eventually one choice. With two, the free lengths satisfy $x+y=n-c$, with fixed lower bounds $x\ge u$, $y\ge v$. The count is eventually $n-c-u-v+1$. The same conclusion holds for any finite signed sum of such counts.

## Decomposable permutations

Every decomposable 1324-avoider has a unique expression $\sigma\oplus\mathrm{id}_m\oplus\tau$, where $m\ge0$, the first component $\sigma$ avoids 132 and the last component $\tau$ avoids 213. Any inversion in an interior component would extend to a 1324 using one point on each side. An occurrence of 132 in the first component or of 213 in the last would also extend. Conversely these restrictions suffice, since the inverted middle pair of any 1324 has to be in a single component. Singleton endpoints are permitted. [Original component description, Lemma 2.1](https://arxiv.org/html/2604.01143v2#S2)

Choose $h$ at least four and at least the maximum length in $B$. For $m\ge h$, replacing $m$ by $m+1$ preserves avoidance in both directions by the interval test. It preserves every inversion and matches these words bijectively with those of length one greater and middle length at least $h+1$. After cancellation, the decomposable contribution to $F_d(n)$ is a signed count of words with $0\le m\le h$.

At length $N$ and inversion count $k$, their two excesses sum to $k-N+m+2$. Here $N$ is $n$ or $n+1$ and $k=n+d$, so this integer depends only on $d,m$ and the choice of side. A negative sum contributes nothing. Otherwise there are finitely many possible pairs of nonnegative excesses. Apply the one-variable lemma independently to the endpoints. For each choice of the two types, the fixed middle and the total length, the representation is unique. The further pattern tests truncate each of the at most two free increasing intervals. The counting argument proves eventual affinity of the decomposable contribution.

## Indecomposable permutations

At length $N$ and fixed excess $e=k-N+1$, there are no indecomposable permutations if $e<0$. For fixed $e\ge0$ and $N\ge e+6$ we have $k\le2N-7$. The theorem of Linusson and Verkama says that every indecomposable 1324-avoider in this region becomes decomposable upon deleting at least one of its four boundary entries. Order these four boundary choices once and assign each word to the first successful choice. Inverse and reverse-complement preserve 1324, length, inversions and decomposability and carry each choice to a first-position deletion. Under such a symmetry, apply the same transformation to the forbidden patterns and to the earlier boundary choices to be excluded. [Linusson–Verkama, Theorem 8](https://arxiv.org/abs/2408.15075) · [Restatement, Theorem 7.1](https://arxiv.org/html/2604.01143v2#S7)

After deleting the first entry and standardizing, write the result as $\sigma\oplus\mathrm{id}_m\oplus\tau$. Put $a=|\sigma|$ and $b=|\tau|$. Reinsert the first entry with value $r$ in one-based notation. The old word’s last proper direct-sum cut is after $a+m$ entries. More generally, after the initial insertion a proper cut occurs precisely after that new entry and an old initial segment of length $j$ that was a cut (including $j=0$) and satisfies $r\le j+1$. This follows by testing whether the first $j+1$ values are exactly the least $j+1$ values. Hence indecomposability is equivalent to $r=a+m+v+1$ with $1\le v\le b$. Inserting $r$ adds $r-1$ inversions, so

```math
e=\operatorname{inv}(\sigma)+e(\tau)+v-1.
```

This bounds $\operatorname{inv}(\sigma)$, $e(\tau)$ and $v$ in terms of $e$. There are finitely many choices for $\sigma$, since $a\le\operatorname{inv}(\sigma)+1$. Apply the one-variable lemma to $\tau$. The middle $m$ is one free increasing interval. The inserted first entry sits above all of it and above exactly $v$ entries of $\tau$. It can split the variable interval of $\tau$ in value order, but at most $v$ of that interval's entries can fall below the new value. To make this uniform, distinguish all lengths up to $v+1$ and retain the first $v+1$ entries of every longer interval in the fixed template. All additional entries then lie above $r$ and form a single remaining increasing interval. We have obtained at most two free intervals for the reconstructed permutation.

Each choice reconstructs at most one permutation for its two specified lengths. Conversely the boundary convention, first entry and direct-sum decomposition recover those choices uniquely. Test 1324-avoidance, avoidance of the transformed $B$, and failure of all earlier boundary deletions by the truncation tests above. The allowed descriptions split into finitely many disjoint rectangles. Their total at length $N$ is eventually affine. This proves eventual affinity of the indecomposable count along every diagonal of fixed excess.

Apply this last result separately to $N=n+1$ with $e=d$ and $N=n$ with $e=d+1$. Subtract their eventual affine functions and add the decomposable contribution. Their sum proves the theorem. ∎
