# Schur positivity of big descents at fixed longest increasing subsequence length

Elizalde, Rivera Jr., and Zhuang conjectured that the big-descent quasisymmetric function of permutations avoiding the increasing pattern of length $m$ is symmetric and Schur positive for every $n$ and $m$. We prove the stronger assertion with the length of the longest increasing subsequence fixed exactly. The Schur coefficients count pairs of tableaux. [Conjecture 4.9, published paper](https://doi.org/10.1007/s00026-026-00805-1) · [Author manuscript, §4.3](https://arxiv.org/html/2408.15111v2#S4.SS3)

## Statement

For a permutation $\pi$ of $[n]$, let $L(\pi)$ be the length of its longest increasing subsequence, with $L(\varnothing)=0$. Write

$$
B(\pi)=\{i:\pi_i>\pi_{i+1}+1\},\qquad
D(\pi)=\{i:\pi_i>\pi_{i+1}\}.
$$

Gessel's fundamental quasisymmetric function $F_{n,S}(X)$ sums the monomials $x_{c_1}\cdots x_{c_n}$ over $c_1\le\cdots\le c_n$ in the positive integers, with $c_i<c_{i+1}$ for $i\in S$. Set $F_{0,\varnothing}=1$. Define

$$
H_{n,d}(X)=\sum_{\substack{\pi\in S_n\\L(\pi)=d}}F_{n,B(\pi)}(X).
$$

Draw partitions in English notation, with row 1 at the top. Write $\lambda'$ for the transpose, $|\lambda|$ for the number of cells, and $\lambda_1$ for the width, taking $\varnothing_1=0$. Two finite counts enter the theorem.

- Let $a_\lambda$ count the standard Young tableaux of shape $\lambda$ in which $i+1$ is never in the cell immediately below $i$.
- Let $e(\rho/\eta)$ count the fillings of the skew shape $\rho/\eta$ by positive integers strictly increasing along rows and down columns, with each entry in row $i$ at most $i-1$. Set the count to zero unless $\eta\subseteq\rho$. An empty filling contributes one.

**Theorem.** For each $\nu\vdash n$ the coefficient of the Schur function $s_\nu$ in $H_{n,d}$ is

$$
\boxed{\displaystyle
[s_\nu]H_{n,d}=
\sum_{\substack{\lambda\subseteq\nu\\\lambda_1=d}}
      a_\lambda\, e(\nu'/\lambda').}
$$

In particular $H_{n,d}$ is symmetric and Schur positive. A permutation avoids the classical pattern $12\cdots m$ precisely when $L(\pi)<m$. Summing over $0\le d<m$ therefore gives both assertions of Conjecture 4.9, including $n=0$ and $m=1$.

## 1. Contract descending intervals of a single color

Put $y_i=x_i/(1-x_i)$ and $Y=(y_1,y_2,\ldots)$. This is an ordinary substitution in each variable. We first show that

$$
\sum_{n\ge 0}H_{n,d}(X)
=\sum_{\lambda_1=d} f^\lambda s_\lambda(Y), \tag{1}
$$

where $f^\lambda$ is the number of standard Young tableaux of shape $\lambda$.

A term on the left is a permutation with a weakly increasing sequence of colors, strictly increasing at big descents. Divide the permutation into its constant-color blocks. Within each such block, every descent drops by exactly one. Cut the block at every ascent. Each resulting piece is a descending interval of consecutive values, possibly a singleton. The intervals are disjoint. Within one color they occur in increasing order of their value ranges, since successive pieces meet at an ascent.

Contract each piece to one letter, label the pieces by their ranks in value order, and retain their colors. The resulting permutation $\tau$ has weakly increasing colors with a strict color increase at every ordinary descent. The longest increasing subsequence length is preserved. An increasing subsequence takes at most one letter per piece, and any increasing subsequence of pieces lifts by taking one letter in each selected piece.

Conversely, start from such a colored $\tau$ and give each position a positive length. In order of increasing rank, allocate disjoint successive intervals of these lengths starting at 1. Replace each position by its interval written in decreasing order, repeating the color. Inside a color block the boundaries between these intervals are ascents. Thus the cuts recover exactly the chosen intervals even when two consecutive blocks have adjacent value ranges. A compressed letter of color $i$ contributes $\sum_{\ell\ge1}x_i^\ell=y_i$.

This bijection gives the sum of $F_{r,D(\tau)}(Y)$ over all compressed permutations of all sizes $r$ with $L(\tau)=d$. Under Robinson–Schensted, the first row of the common shape has length $d$, and the descent set of $\tau$ is the descent set of its recording tableau. For a fixed shape $\lambda$, the insertion tableau has $f^\lambda$ choices. The sum of the fundamentals over the recording tableaux is $s_\lambda$, by standardization of semistandard tableaux. This proves (1).

## 2. Expand by width before substituting

Write $G_\lambda$ for the signed stable Grothendieck function in Buch's convention and $g_\lambda$ for its Hall-dual. Use the signless version

$$
U_\lambda(Y)=(-1)^{|\lambda|}G_\lambda(-Y),
$$

where $-Y$ means negating each variable. The following three established identities specify all the Grothendieck-function input to the proof.

1. Lenart's expansion gives $U_\lambda=\sum_{\rho\supseteq\lambda}e(\rho/\lambda)s_\rho$. Each shape on the right with nonzero coefficient has $\rho_1=\lambda_1$, because an added cell in row 1 would require a positive entry at most zero. [Buch, Theorem 6.11 and (6.5)](https://arxiv.org/pdf/math/0004137)
2. The Cauchy kernels $\sum_\lambda G_\lambda(Y)g_\lambda(Z)$ and $\sum_\mu s_\mu(Y)s_\mu(Z)$ coincide. The function $g_\lambda$ enumerates reverse plane partitions of shape $\lambda$ with weakly increasing rows and columns. The exponent of $z_i$ counts columns containing $i$. [Lam–Pylyavskyy, §9.1 and Theorem 9.15](https://arxiv.org/pdf/0705.2189) · [Yeliussizov, Corollary 5.5](https://arxiv.org/pdf/1711.09544)
3. With $\omega(s_\rho)=s_{\rho'}$, the substitution in (1) satisfies $U_\lambda(Y)=\omega(U_{\lambda'})(X)$. Indeed $U_\lambda=G^{(0,1)}_\lambda$ in Yeliussizov's convention. Substitution produces $G^{(1,0)}_\lambda$, which is $\omega(G^{(0,1)}_{\lambda'})$. [Yeliussizov, Proposition 3.4 and Theorem 5.4](https://arxiv.org/pdf/1601.01581)

For the next calculation regard $Y$ as independent variables. On symmetric functions of bounded degree in $Z$, define the linear functional

$$
\Phi(h)=\sum_{r\ge 0}[z_1z_2\cdots z_r]h(Z).
$$

The coefficient specifies exponent zero for every variable outside the monomial, and $r=0$ extracts the constant. In particular $\Phi(s_\mu)=f^\mu$ since distinct entries $1,\ldots,|\mu|$ give standard tableaux.

Negate both alphabets in the Cauchy identity. The ordinary Schur kernel is unchanged by homogeneity. Apply $\Phi$ in $Z$. This gives

$$
\sum_\mu f^\mu s_\mu(Y)
=\sum_\lambda U_\lambda(Y)\,\Phi\!\left((-1)^{|\lambda|}g_\lambda(-Z)\right). \tag{2}
$$

All operations are degreewise finite. At any bounded $Y$-degree only finitely many $\lambda$ occur, since $U_\lambda$ starts in degree $|\lambda|$, and $g_\lambda$ has degree at most $|\lambda|$.

## 3. The signed coefficient counts standard tableaux

Consider a reverse plane partition contributing to $[z_1\cdots z_r]g_\lambda$. Each label $1,\ldots,r$ occurs in exactly one column. Its occurrences form one vertical interval by weak monotonicity. Replace the occurrences of 1 by successive integers from top to bottom, then those of 2, and so on. Rows had no repeated label, so this produces a standard tableau $T$. Mark each adjacent pair of successive integers created from a single label.

Conversely, in a standard tableau choose any subset of the pairs for which $i+1$ is immediately below $i$. Merge the labels of each marked run and renumber the resulting groups consecutively. The result is a reverse plane partition with each label confined to one column. The two operations are inverses, including when successive marked pairs share a cell.

If $M$ is the set of marks, $r=|\lambda|-|M|$, so the sign of the standardized object in (2) is $(-1)^{|M|}$. For a tableau with $b$ eligible pairs the sum over its marks is $(1-1)^b$. Thus

$$
\Phi\!\left((-1)^{|\lambda|}g_\lambda(-Z)\right)=a_\lambda. \tag{3}
$$

Project (2) in its $Y$ alphabet onto the span of the Schur functions of first-row length $d$. Identity 1 above implies that this projection keeps the entire $U_\lambda$ exactly when $\lambda_1=d$, and otherwise kills it. We obtain

$$
\sum_{\mu_1=d}f^\mu s_\mu(Y)=\sum_{\lambda_1=d}a_\lambda U_\lambda(Y).
$$

Now substitute $y_i=x_i/(1-x_i)$. By (1) and identity 3 the resulting series is

$$
\sum_{n\ge0} H_{n,d}(X)=\sum_{\lambda_1=d}a_\lambda\,\omega(U_{\lambda'})(X).
$$

Lenart's expansion of $U_{\lambda'}$ makes the coefficient of $s_\nu$ on the right precisely the boxed formula. Extracting homogeneous degree $n$ proves the theorem. $\square$

## Example

For $n=4$ and $m=3$, the formula gives

$$
Q_4^{(1)}(123)=4s_{(4)}+2s_{(3,1)}+2s_{(2,2)}.
$$

For instance, the two contributions to $s_{(2,2)}$ come from $\lambda=(2,1)$ and $(2,2)$, each with one admissible standard tableau and one flagged filling. This agrees with Table 10 of the source paper. The checker compares the two sides separately at each exact longest increasing subsequence length. [Exact checker](verify.py)
