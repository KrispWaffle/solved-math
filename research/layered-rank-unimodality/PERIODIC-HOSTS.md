# Powers of an arbitrary composition

**Theorem.** Fix any nonempty composition $v$. For all sufficiently large $m$, the principal ideal below the concatenation $v^m$ is rank-unimodal. The period can contain any number of descents and arbitrary positive letters. For periods containing a letter of size at least two the peak has an explicit location up to the choice between two adjacent integers, and the weight of a uniformly chosen distinct subword has a Gaussian limit after centering and scaling. Yonezu's alternating two-valued theorem covers every repetition in that family. The threshold here may depend on the entire period. [Vatter's conjecture](https://arxiv.org/pdf/2602.16355v4#page=7) · [Yonezu, Lemma 2 and Theorem 1](https://zenodo.org/records/23954556)

## Exact reduction to powers of one polynomial

Let $F_W$ be the distinct-subword rank polynomial and $D=|v|$ its period weight. Split $v=U,M,V$ at any one of its largest letters. Write $Z=VU$, $S=x+\cdots+x^M$, and $E(W)=1+(S-1)F_W$. The maximal-part identity gives $E(X,M,Y)=E(X)E(Y)$ for any arms whose letters are at most $M$. The gaps between successive marked copies of $M$ in $v^m$ are all $Z$. Hence $E(v^m)=E(v)E(Z)^{m-1}$. Put $Q=E(Z)$, $G=F_Z$ and $H=F_v$. Cancellation of $S-1$ gives the exact identities
```math
F_{v^{m+1}}=G+Q F_{v^m},\qquad
F_{v^m}=G\sum_{j=0}^{m-2}Q^j+H Q^{m-1}. \tag{1}
```
The first sum in (1) is empty for $m=1$. The polynomial $Q=F_{Z,M}-F_Z$ counts actual words. Its positive support is an integer interval. Starting from a minimum-weight word in this difference, fix an embedding into $Z,M$. Restore its chosen letters to their capacities and insert the missing letters one unit at a time until the host is reached. At every step the larger word still contains the starting word and remains outside the ideal of $Z$. If $M\ge2$, the host and its variant with final letter $M-1$ both have weight greater than $|Z|$. Thus $Q$ has at least two adjacent positive coefficients, and $q=Q(1)>1$. For $M=1$ the host is all ones and every available rank has one member. [Peak identity](FIXED-NUMBER-OF-PARTS.md)

## Two local coefficient estimates

Assume $M\ge2$. Normalize the coefficients of $Q$ to a probability distribution by dividing by $q$. Let $\mu,\sigma^2,\kappa_3$ be its mean, variance and third centered moment. Here $\mu>0$ and $\sigma^2>0$. For a fixed nonzero polynomial $B$ with nonnegative coefficients, put $\mu_B=B'(1)/B(1)$ and $b_{j,n}=[x^n]BQ^j$. With $s=n-j\mu$ and with any fixed $K$, the estimates below hold uniformly for $|s|\le K\log j$:
```math
\frac{b_{j,n+1}-b_{j,n}}{q^jB(1)/(\sqrt{2\pi}\,\sigma^3j^{3/2})}
 =-s+\mu_B-\frac12-\frac{\kappa_3}{2\sigma^2}+o(1),
```
```math
\frac{b_{j,n+1}-2b_{j,n}+b_{j,n-1}}
     {q^jB(1)/(\sqrt{2\pi}\,\sigma^3j^{3/2})}=-1+o(1).
```
For a direct derivation use Fourier inversion with $\phi(t)=Q(e^{it})/q$. The multipliers for the two differences are $e^{-it}-1$ and $2\cos t-2$. The adjacent positive coefficients ensure $|\phi(t)|<1$ on $0<|t|\le\pi$. Near the origin
```math
\log\phi(t)=i\mu t-\sigma^2t^2/2-i\kappa_3t^3/6+O(t^4).
```
Set $t=y/\sqrt j$. On $|y|\le\log j$, expand $e^{-ist}B(e^{it})/B(1)=1+i(\mu_B-s)y/\sqrt j+O((1+|s|)^2y^2/j)$. In the first integral the odd leading term vanishes. The two even terms at the next order are $(\mu_B-s-1/2)y^2$ and $-\kappa_3y^4/6$ times the Gaussian density factor. The ratio of its fourth to second moment integral is $3/\sigma^2$. The centered second difference gives $-y^2$ at this order. On the expanding inner interval Taylor remainders after normalization are bounded by a fixed power of $\log j$ divided by $\sqrt j$. The omitted Gaussian tails are smaller than every inverse power of $j$ and the outer arc is exponentially small. This proves both estimates.

## One change of direction

Odlyzko and Richmond's theorem gives log-concavity of the coefficients of $Q^j$ for all sufficiently large $j$, after shifting its minimum exponent to zero. The first local estimate with $B=1$ brackets all its modes between $j\mu-C$ and $j\mu+C$ for a constant $C$. For each of $B=G,H$, summing over the finitely many shifts in $B$ gives nonnegative forward differences below $j\mu-C'$ and nonpositive ones above $j\mu+C'$. Enlarging $C'$ accommodates the finitely many smaller powers. [Odlyzko–Richmond, Theorem 1](https://www-users.cse.umn.edu/~odlyzko/doc/arch/unimodal.convolut.pdf)

The finite host theorem of Pouzet and Rosenberg already gives increase through the midpoint of total weight $mD$. Consider a rank $n\ge mD/2$ on the lower side, $n\le m\mu-K_0\log m$. Only indices $j\le n/\mu+O(1)$ in (1) can give a negative forward difference. Their combined absolute contribution is $O(q^{n/\mu})$. Choose a constant $A$ with $A\log q>2$, and then $K_0>A\mu+3$. The term $GQ^j$ with $j=\lfloor n/\mu+A\log m\rfloor$ is present, has $j$ bounded above and below by positive multiples of $m$, and has $n-j\mu=-A\mu\log m+O(1)$. Its forward difference is bounded below by a positive constant times $q^j\log(m)/m^{3/2}$. This dominates the entire possible negative contribution. All ranks in this lower range therefore increase. At $n\ge m\mu+C'$ every summand in (1) has nonpositive forward difference.

It remains to compare adjoining differences within $|n-m\mu|\le K_0\log m+2$, enlarging the fixed additive margin to cover the upper transition for large $m$. Choose $A'$ such that $A'\log q>2$. All terms with $j\ge m-A'\log m$ have strictly negative second differences there, by the second local estimate. The last term $HQ^{m-1}$ alone contributes a negative amount of magnitude at least a positive constant times $q^{m-1}/m^{3/2}$. The absolute sum of the second differences from earlier indices is $O(q^{m-A'\log m})$, which is smaller. Thus the consecutive forward differences in the middle decrease strictly. This connects the two outer sign ranges and proves eventual unimodality. The first-half result used above counts distinct patterns of the layered permutation, which equal the distinct generalized subwords here. [First-half theorem](../principal-pattern-rank-unimodality/FirstHalf.lean)

## Location and typical weight

On a fixed small arc about $x=1$, the multiplicative factor for the largest power in (1) is
```math
B_*(x)=H(x)+\frac{G(x)}{Q(x)-1},\qquad
F_{v^m}(x)=B_*(x)Q(x)^{m-1}-\frac{G(x)}{Q(x)-1}.
```
It is analytic on that arc, $B_*(1)>0$, and its derivatives are real at one. On the complementary unit-circle arc use the finite formula (1), which is exponentially smaller than $q^{m-1}$ up to a polynomial factor. Therefore the same local first-difference expansion applies with $j=m-1$ and $\mu_B=B_*'(1)/B_*(1)$. All possible modes, for sufficiently large $m$, are among the nearest integer or integers to
```math
(m-1)\mu+\frac{B_*'(1)}{B_*(1)}-\frac{\kappa_3}{2\sigma^2}.
```
Indeed, the difference at $n$ has the sign of this number minus $n+1/2$ whenever its distance from zero stays bounded below in the logarithmic window. The mean and correction are rational, so the nonzero distances in question have a fixed positive lower bound over all $m$. Together with the established unimodality this leaves only the indicated candidates. In a half-integer case one or both of the two adjacent candidates can be a mode.

For the rank of a uniformly chosen distinct word, differentiating the local formula at one gives mean $(m-1)\mu+B_*'(1)/B_*(1)+o(1)$ and variance $(m-1)\sigma^2+O(1)$. Its characteristic function at $t/\sqrt{m-1}$, after subtracting the mean, tends to $\exp(-\sigma^2 t^2/2)$ by the same Taylor expansion. This gives the Gaussian limit along all repetitions. ∎
