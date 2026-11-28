# A partition formula for the stable inversion counts

Let $L_k$ be the eventual number of permutations of length $n$ with exactly $k$ inversions that avoid 1243. An occurrence uses positions in increasing order whose values have the relative order indicated. Write $P(q)=\prod_{j\ge1}(1-q^j)^{-1}$. For a finite set $C$ of positive integers, let $R(C)=\{c\in C:c-1\notin C\}$ be the smallest members of its consecutive runs.

**Theorem.** The answer to Claesson, Linusson, Ulfarsson and Verkama's Problem 8.3 is

```math
\sum_{k\ge0}L_k q^k=P(q)
\sum_{s\ge0}\ \sum_{1\le c_1<\cdots<c_s}\,
\sum_{\substack{0\le u_1<\cdots<u_s\\u_i<c_i\ (1\le i\le s)}}
 q^{\sum_{i=1}^s u_i+\sum_{c\in R(\{c_1,\ldots,c_s\})} c}. \tag{1}
```

The empty pair of lists contributes one. Equivalently, $L_k$ counts triples consisting of an ordinary integer partition and the two strictly increasing lists in (1), with total weight $k$ as indicated. No unknown permutation enumeration occurs in the right side. Each coefficient is finite. The sum of the $u_i$ is at least $s(s-1)/2$, and each run of $c_i$ starts at most at $k$ and contains at most $s$ members. [Source, Problem 8.3](https://arxiv.org/html/2604.01143v2#S8)

## Inserting a new minimum

Start from the empty permutation. At a step, increase all old values by one and insert a new one after $i$ old entries, with $0\le i\le n$ for an old permutation of length $n$. This adds precisely $i$ inversions. Removing the smallest value recovers the old permutation and the slot. Number positions from one. Let $a$ be the rightmost position starting a 132 occurrence and $b$ the rightmost starting position of an inversion. A missing starting position has value zero. Then $0\le a\le b$. Any occurrence of 132 starts strictly before the inversion in its own last two entries.

Suppose the old permutation avoids 1243. Any newly created 1243 must start with the new minimum and needs a 132 to its right. Thus precisely the slots $i\ge a$ are allowed. If $a\le i<b$, an old inversion starts to the right of the slot, so the new minimum starts a 132 at position $i+1$. All old 132 starts are at most $i$. The rightmost old inversion start shifts from $b$ to $b+1$. If $i\ge b$, the suffix after the slot is increasing and there is no new 132. The last preceding entry starts an inversion to the new minimum if $i>0$. This gives the updates

```math
(a,b)\longmapsto
\begin{cases}(i+1,b+1),&a\le i<b,\\(a,i),&b\le i.\end{cases} \tag{2}
```

At $i=0=b$ the second line returns $(0,0)$. Distinct finite histories of a specified length give distinct permutations since deletion recovers every slot. Every avoider is obtained because each deletion preserves avoidance.

## Removing the length parameter

Discard all initial zero-cost steps at $(0,0)$. A nonempty reduced history starts with a positive slot and then always has $a<b$. At such a state a zero-cost step can occur only when $a=0$, in which case the first line sends $a$ to one. The first coordinate never decreases, so at most one zero-cost step remains. Let a nonempty reduced history of total cost $k$ have $h$ steps. Besides any chosen positive slot $i$, at least $h-2$ of the other slots are positive. Thus $i\le k-h+2$, and $h\le k+1$. Conversely, any such path of (2), even with slots chosen without a length bound, becomes legal at every length $n\ge k+2$ by starting from an identity with $n-h$ entries. It already has room for every positive slot before the first step. This operation is inverse to stripping a history for that $n$. For $k=0$ it selects the identity. For every $k\ge1$ the threshold is sharp. The reduced history $(k,0)$ has first state $(0,k)$ and cannot fit at length $k+1$. Every legal history at that length still injects into the stable collection. Thus the stable coefficient is strictly larger than the preceding one. The source's component argument also supplies the upper threshold. [Stabilization](https://arxiv.org/html/2604.01143v2#S5.SS1)

## From paths to ordinary partitions

Along a nonempty reduced path the level $b$ is positive and weakly increasing. An ordinary transition (second line of (2)) arrives at any level $b'\ge b$ with weight $b'$ and keeps $a$. A marked transition (first line) goes from level $c$ to $c+1$ with weight $u=i$, where $a\le u<c$, and changes $a$ to $u+1$. The set $C$ of levels immediately preceding marked transitions therefore has distinct positive members in increasing order. The corresponding weights $u$ increase strictly, since a marked transition sets $a$ to its weight plus one and ordinary moves preserve $a$.

For each positive level $b$ record the number of ordinary arrivals there. At the first level of a run of $C$, at least one ordinary arrival is mandatory. Indeed, the marked exit must be reached, and there is no marked arrival from $b-1$. At every other level the ordinary multiplicity is an arbitrary nonnegative integer. This includes a level with a marked arrival, where all ordinary moves occur after that arrival. Subtract one ordinary arrival at each $b\in R(C)$. The remaining ordinary arrivals form an unrestricted integer partition by assigning a part $b$ per arrival. The removed arrivals have total weight $\sum_{b\in R(C)}b$.

Conversely, from any such partition and lists, restore one part at each run start. Process levels in increasing order. When the preceding level has a marked exit, that exit supplies the first arrival. Perform the prescribed ordinary arrivals, then take the prescribed marked exit if present. A marked exit always has its source level occupied, either by a mandatory ordinary arrival or by the preceding marked transition. The conditions on the $u_i$ give exactly $a\le u_i<c_i$ at that step. Every ordinary arrival is permitted, including a jump across unused levels. This reconstructs a unique reduced history, including the empty history. Summing its weight proves (1). ∎

The same triples determine the finite-length distribution. Reconstruct their chronological slots $i_1,\ldots,i_h$ by the inverse map above, and put $p=\max(\{0\}\cup\{i_j-j+1:1\le j\le h\})$. Before step $j$ the available length is the initial padding plus $j-1$. Thus the triple occurs once at every length $n\ge h+p$. If $z$ marks length and $q$ marks inversions, the complete bivariate enumerator is $(1-z)^{-1}\sum z^{h+p}q^k$, summed over exactly the triples in (1) of all weights $k$. For the empty triple, both exponents are zero.

## All patterns with a single inversion

Write $\iota_r$ for the increasing permutation of length $r$, allowing the empty permutation, and $\oplus$ for direct sum. Every pattern with exactly one inversion is $\iota_r\oplus21\oplus\iota_s$ for unique nonnegative $r,s$. Let $L_{r,s}(q)$ be its stable inversion series. Then

```math
L_{r,s}(q)=L_{r,0}(q)L_{s,0}(q). \tag{3}
```

This product is a consequence of the confinement argument in the proof of Claesson, Linusson, Ulfarsson and Verkama's Proposition 5.1. Their proof identifies the first $r$ and last $s$ direct-sum components that can contain inversions. The $r=s=1$ two-partition formula is due to Claesson, Jelínek and Steingrímsson. [Confinement and stabilization](https://arxiv.org/html/2604.01143v2#S5.SS1) · [Original 1324 result](https://doi.org/10.1016/j.jcta.2012.05.006)

Here is the product argument. Each direct-indecomposable component of size $d$ uses at least $d-1$ inversions. Indeed, in its inversion graph every position between the endpoints of an edge is adjacent to at least one endpoint. Connected components of the graph therefore occupy position intervals, ordered as their value intervals. Direct indecomposability means the graph is connected. Summing the edge bound over its components shows that a length-$n$ permutation with $k$ inversions has at least $n-k$ direct components.

Take $n\ge k+r+s$. Keep the first $r$ components as a left word and the last $s$ as a right word, allowing either list to be empty. Every intermediate component must be a singleton, since an inversion there would extend to the forbidden pattern by using one entry in each of the designated components. The left word avoids $\iota_r\oplus21$, since the $s$ components on its right could complete any such occurrence. The right word avoids $21\oplus\iota_s$ by the same argument. Conversely, given an avoiding left word with exactly $r$ components and an avoiding right word with exactly $s$, their combined length is at most $k+r+s$. Insert the unique intervening run of singleton components that gives length $n$. Every inversion is confined to one of the two words, preventing the full forbidden occurrence. Thus this is a bijection. Applied with $s=0$, the same argument identifies the stable one-sided series with the inversion series of the left words of exactly $r$ components. Reverse-complement gives the right-word enumeration. Inversions add under direct sum, proving (3). For $r=0$ the corresponding one-sided series is one. In particular (1) agrees with the actual length-$n$ coefficient whenever $n\ge k+2$.
