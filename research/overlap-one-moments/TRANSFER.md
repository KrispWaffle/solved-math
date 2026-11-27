# A return-walk representation for the raw packing counts

Let $A_r=N(r+1)$ and $a,b,c$ be the parameters in the [target statement](README.md). Write $d=a+b+c$. The first window has $a+c$ elements strictly below its last endpoint and $b$ above it. For any linear extension of a longer stack, use $(x,y)$ for the additional numbers below and above its last endpoint beyond these two minima. Both are nonnegative.

## Extending a stack

A new window shares the old endpoint. Its $a$ new lower elements form a chain below that endpoint. Its $c-1$ intermediate elements, new endpoint, and $b$ new upper elements occur in that order above the old endpoint. If $v$ of the old upper elements precede the new endpoint, then $0\le v\le y+b$. The number of extensions with that choice is

```math
\binom{x+2a+c}{a}\binom{v+c-1}{c-1}\binom{y+2b-v}{b}.
```

The three factors interleave the old and new chains below the old endpoint, between the endpoints, and above the new endpoint, respectively. The new state is $(x+a+c+v,y+b-v)$. The old extension is recovered by restriction, so this counts each extension once. This step is the overlap-one endpoint recurrence of Part I in shifted coordinates. [Part I, Theorem 4.7](https://arxiv.org/html/2610.29846v1#S4.SS2)

Define $T$ on functions by summing the value at each new state with these weights. Then $A_r=(T^r1)(0,0)$, since the one-window stack has exactly one extension at $(0,0)$.

## A matrix with the right return counts

Set $B_{p,q}(x,y)=\binom{x}{p}\binom{y}{q}$. Define $M_{(p,q),(i,k)}$ as the coefficient of $B_{i,k}$ in $TB_{p,q}$. For each fixed pattern this is a single matrix, independent of $r$.

**Proposition.** The matrix is row-finite and column-finite, its entries are nonnegative integers, and

```math
 A_r=(M^r)_{(0,0),(0,0)}\qquad (r\ge0).
```

To see nonnegativity, put $h=y+b$ and $w=h-v$. The new state's basis term is $\binom{x+a+c+v}{p}\binom{w}{q}$. Expand the first factor among $x$, $a+c$, and $v$ by Vandermonde's identity. The three interleaving weights are translated binomial functions of $x$, $v$, and $w$, respectively. Every translation is by a nonnegative integer, so another application of Vandermonde expands each of them with nonnegative coefficients. Products of two basis terms in one variable also have nonnegative integer coefficients. For sets of sizes $i,j$, the coefficient of $\binom{n}{k}$ in $\binom{n}{i}\binom{n}{j}$ counts ordered pairs of subsets of a fixed $k$-element set whose union is that whole set. Finally the sum over splittings $v+w=h$ uses

```math
\sum_{v+w=h}\binom{v}{i}\binom{w}{j}
=\binom{h+1}{i+j+1}=\binom{y+b+1}{i+j+1}.
```

The last expression again has nonnegative binomial coefficients in $y$. This proves the asserted positivity without sign cancellation. The total degree is at most $p+q+d$, including the extra degree from summing over $v$. Thus each row has finite support. Each column is finite as well. Its coefficient is the mixed forward difference of $TB_{p,q}$ at zero, of orders $i,k$. Only evaluations at $x\le i$, $y\le k$ enter this difference. Every new state there has coordinate sum $x+y+d$, so these evaluations all vanish for $p+q>i+k+d$.

Iterating the change of basis computes $T^r B_{0,0}$ with coefficients given by row $(0,0)$ of $M^r$. At $(0,0)$ only the constant basis function survives. This proves the return identity. In particular, the counts admit a renewal decomposition: the first-return weights at every positive length are nonnegative integers. Concatenating two return walks gives $A_{r+s}\ge A_rA_s$ for arbitrary $r,s$.

## Why this matrix does not settle Conjecture 10.6

Total nonnegativity of a suitably ordered production matrix would imply the desired Hankel positivity. Already for $a=b=1,c=3$ (for example the pattern 213465), this matrix cannot be made totally nonnegative by any ordering of its states. Choose the ordered pairs $U=((0,0),(1,1))$ and $V=((0,2),(2,0))$. Direct mixed differences in the displayed transfer give

```math
M_{U,V}=\begin{pmatrix}50&0\\550&4\end{pmatrix},
\qquad
M_{V,U}=\begin{pmatrix}0&3\\210&456\end{pmatrix}.
```

The determinants are $200$ and $-630$. Reversing either pair changes the signs of both determinants. Thus their product stays negative in every total ordering. These are minors of the transfer matrix. Positivity of the two Hankel matrices of the **packing sequence** remains open. [Exact check](transfer.py) · [Production-matrix criterion, Theorem 9.7](https://arxiv.org/html/1807.03271v2)
