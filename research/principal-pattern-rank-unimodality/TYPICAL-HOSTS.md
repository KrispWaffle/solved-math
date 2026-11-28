# Rank-unimodality for almost every host permutation

Let $D_m(\pi)$ be the number of distinct classical patterns of length $m$ in a uniform permutation $\pi\in S_n$. For every fixed $0<a<1$,
```math
\mathbb P\big(D_m^2>D_{m-1}D_{m+1}\text{ for every }
\lceil an\rceil\le m<n\big)\longrightarrow1 .
```
In particular the principal permutation downset is rank-unimodal with probability tending to one. This proves an asymptotic case of Vatter's Conjecture 2.1. The conjecture quantifies over every host. [Original problem](https://arxiv.org/pdf/2602.16355v4#page=4)

## Reducing the counts to a small set of positions

Write $f_m=D_m/\binom nm$. Couple the uniform sets $S_m$ of positions by one random ordering, independent of the plot of $\pi$. Conditional on the plot $f_m=\mathbb E[1/K_m\mid\pi]$, where $K_m$ is the number of $m$-sets with the same pattern as $S_m$. Fix $t=\lfloor an/2\rfloor$. We use the existing simultaneous insertion bounds to obtain an error smaller than any prescribed inverse power of $n$. [Simultaneous bounds](../../results/distinct-random-permutation-patterns/UNIFORM-PROFILE.md)

Fix $A>0$, take $L=\lceil\log n\rceil$, and call a map large if it moves more than $L$ labels. For $L<l\le8n/\log n$ the expected number of moving path systems on $l$ edges with a specified number of components, preserving both orders at *some* $m\ge t$, is bounded by
```math
\big(C_a\sqrt{\max(8/\log n,1/L)}\big)^l .
```
After summing over at most $l$ component counts and over $l>L$, this is $o(n^{-A})$, since the base tends to zero. Above $8n/\log n$ the bound $(n+1)2^n/\lceil4n/\log n\rceil!$ is exponentially small. Also, except with probability $O(n^{-A})$, every run of consecutive positions containing no $S_t$ label in either of the two orders has length at most $R=C_{a,A}\lceil\log n\rceil$. For a specified run of $R$ labels the hypergeometric avoidance probability is at most $(1-t/n)^R$, and there are at most $2n$ starts.

Outside these events, each edge of a preserving map has both displacements at most $D=(L+1)(R+1)$. Indeed no fixed red can lie strictly between its endpoints in either coordinate. At most $L$ labels of $S_t$ in that interval are moved reds, so the interval is the union of at most $L+1$ gaps together with these labels. An individually allowable pair itself gives a preserving map and satisfies the same bound.

Call the plot separated if every distinct pair with both positive displacements at most $D$ has a disjoint set of determining labels, its horizontal and vertical open strips have no common label, and the closed coordinate intervals of different pairs are disjoint on each axis. For this polylogarithmic $D$, separation has probability tending to one. To spell out the quantitative dependence, for a triple consisting of one close pair and an extra point in both its strips there are $O(nD^2)$ assignments on each axis and probability $1/(n)_{\underline3}$ for each combined specification. Two pairs with a common endpoint admit the same bound. For two distinct pairs with horizontal overlap there are $O(nD^3)$ choices horizontally and $O(n^2D^2)$ vertically with probability $1/(n)_{\underline4}$; exchange the two axes for a vertical overlap. For a fifth point in a horizontal strip of one pair and a vertical strip of another the bounds are $O(n^2D^3)$ on each axis with probability $1/(n)_{\underline5}$. The sum is $O((1+D)^6/n)$. The meanings of the strips and all three kinds of obstruction are given in the distribution proof. [Plot-pair calculation](../../results/distinct-random-permutation-patterns/LIMIT-LAW.md)

There are at most $2D^2$ such pairs in expectation, so with probability tending to one there are at most $D^3$ of them. Let $B$ be the union of their endpoints and all labels in their coordinate strips. On these plots $|B|\le2D^4$. Every preserving map on the good flag event consists of vertex-disjoint single replacements, because a path with two edges would have two distinct close pairs with a shared vertex. The edge intervals are disjoint and contain no other red, and conversely any collection of the individual replacements preserves both orders. Hence, simultaneously at all $m\ge t$, the class has exactly $2^{W_m}$ elements, where $W_m$ counts the allowable close pairs and depends only on $S_m\cap B$. On the separated plot define $h(U)=2^{-W(U)}$ for each $U\subseteq B$ using these local tests, and put $g_m=\mathbb E[h(S_m\cap B)\mid\pi]$. Markov's inequality for the conditional probability of the exceptional flag event, taking $A=10$, proves that with probability tending to one over the plot,
```math
|B|=O_a((\log n)^8),\qquad
\max_{t\le m\le n}|g_m-f_m|\le n^{-4}.
```
Only the exceptional flag requires the inverse-power bound. All the geometric separation conditions depend on the plot alone.

## Differences on a slice of the Boolean lattice

For any fixed $B\subseteq[n]$ and $0\le h\le1$, the above averages satisfy $|g_{m+1}-g_m|\le |B|/n$. The new element of the flag is uniform and contributes only when it belongs to $B$. For the second difference, let $x,y$ be the next two labels after $S_m$. They are exchangeable given $S_m$. With $H(S)=h(S\cap B)$ the second difference is exactly the expectation of
```math
H(S_m+x+y)-H(S_m+x)-H(S_m+y)+H(S_m).
```
This vanishes unless both $x,y\in B$, and its absolute value is at most two. Consequently $|g_{m+2}-2g_{m+1}+g_m|\le 2|B|(|B|-1)/(n(n-1))$ for every $m\le n-2$.

The uniform profile law on $[a/3,1]$ has an almost surely strictly positive minimum, since its limiting product is positive and continuous there. Thus with probability tending to one $f_m\ge n^{-1/8}$ for every $m\ge t$. Combine this with the preceding approximation. The absolute values of the first and second differences of $f$ in this range are at most $O_a((\log n)^8/n)+2n^{-4}$ and $O_a((\log n)^{16}/n^2)+4n^{-4}$. Since $0\le f_m\le1$, expanding $f_{m-1}f_{m+1}$ about $f_m$ gives, uniformly for $\lceil an\rceil\le m<n$,
```math
\frac{f_{m-1}f_{m+1}}{f_m^2}\le 1+
O_a\!\left(\frac{(\log n)^{16}}{n^{7/4}}\right)=1+o(1/n).
```
The binomial coefficient ratio is exactly $(m+1)(n-m+1)/(m(n-m))=1+(n+1)/(m(n-m))\ge1+4/n$. It follows that $D_m^2>D_{m-1}D_{m+1}$ at all the stated ranks. [Positivity and uniform convergence](../../results/distinct-random-permutation-patterns/UNIFORM-PROFILE.md)

Pouzet and Rosenberg proved that the principal rank counts are nondecreasing up to the midpoint for every host. Use the preceding conclusion with, for instance, $a=1/3$. In the overlapping range the ratios $D_{m+1}/D_m$ become strictly decreasing and can cross one at most once. Together these statements prove unimodality with probability tending to one. [First-half theorem](https://www.sciencedirect.com/science/article/pii/S0195669886800075)
