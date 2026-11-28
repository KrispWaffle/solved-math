# An exponential comparison near the maximum inversion count

Let $D$ be a permutation class closed under direct sum and containing every decreasing permutation. Write $b_n(j)$ for its number of length-$n$ members with $j$ inversions, and $\lambda=\limsup_n |D_n|^{1/n}$. The direct sum puts an entire first permutation below and before a second. Length and inversion counts both add, and prescribed block lengths make concatenation injective.

For $C>0$ put $G(C)=(1+C)^{1+C}/C^C$, and put $G(0)=1$. For any $C\ge0$ with $G(C)<\lambda$, there exist $\eta>0$ and $N$ such that
```math
b_{n+1}(n+j)\ \ge\ e^{\eta n}\,b_n(j)
\qquad(n\ge N,\ 0\le j\le Cn).
```
The theorem compares individual coefficients uniformly. The same proof works if $\log G(C)$ is replaced by any strict upper bound below $\log\lambda$ on the limiting exponential rate of the source coefficients in that strip.

**Three ingredients.** First, the Lehmer code of each source permutation is a vector of $n$ nonnegative integers of sum $j$. For $0<x<1$ the number of such vectors is at most $x^{-j}(1-x)^{-n}$. For $C>0$ take $x=C/(1+C)$ to obtain $b_n(j)\le G(C)^n$. At $C=0$ there is only the identity.

Second, there is a fixed finite family $H\subset D_m$ whose members all have the same inversion count and whose entropy $h=m^{-1}\log|H|$ exceeds $\log G(C)$. Indeed, choose a length where $|D_m|$ exceeds $G(C)^m$ by an exponential factor. There are only $1+\binom m2$ possible inversion counts. Write $y$ for the common inversions per point in this fixed family.

Third, every integer $T\ge0$ is realized by a direct sum of decreasing blocks on at most $3\sqrt{2T}+3$ points. Use a decreasing block of largest length $d$ with $\binom d2\le T$ and then $T-\binom d2<d$ copies of 21. Any prescribed larger length is obtained by adding singleton blocks. In particular every coefficient in the source strip has a positive count for all sufficiently large lengths.

**Uniformity.** Suppose there were no such $\eta,N$. There would be $n_i\to\infty$ and integers $0\le j_i\le Cn_i$ with
```math
b_{n_i+1}(n_i+j_i)<e^{n_i/i}b_{n_i}(j_i).
```
Pass to a subsequence on which $j_i/n_i\to\rho$ and $n_i^{-1}\log b_{n_i}(j_i)\to s\le\log G(C)$. Choose $\delta>0$ with $h>\log G(C)+3\delta$ and a fixed $0<\theta<1/2$ with $\theta y<1/8$. Pick one member of the subsequence far enough out that the whole family $A$ of words at that length and inversion count has density $x<\rho+1/8$ and entropy $a>s-\theta\delta$. Fix that length $l$ and this family from now on.

At a large target length $n_i+1$, reserve $R_i=\lceil3\sqrt{2(C+1)n_i}\rceil+4$ positions. Set $L_i=n_i+1-R_i$. Use $\lfloor(1-\theta)L_i/l\rfloor$ blocks from $A$, followed by $\lfloor\theta L_i/m\rfloor$ blocks from $H$. All these blocks have individual fixed lengths and inversion counts. Their combined inversion total divided by $n_i$ tends to $(1-\theta)x+\theta y<\rho+1/4$. The target density tends to $\rho+1$. The number $T_i$ of remaining required inversions is therefore nonnegative for all large $i$ and is at most $(C+1)n_i$. The reserved positions suffice for the exact decreasing-block construction. Pad any rounding remainder with singletons. The fixed block boundaries recover all choices.

The resulting lower limit for $n_i^{-1}\log b_{n_i+1}(n_i+j_i)$ is at least $(1-\theta)a+\theta h>s+2\theta\delta$. The assumed failure gives an upper limit at most $s$, a contradiction. ∎

**Principal 1324 consequence.** The pattern 4231 is direct-sum indecomposable and contains an ascent, so $D=\operatorname{Av}(4231)$ satisfies the hypotheses. Complement preserves length and sends $k$ to $\binom n2-k$. Thus for every $C$ with $G(C)<\operatorname{gr}(\operatorname{Av}(1324))$ the source conjecture holds with an exponentially growing ratio, uniformly whenever $0\le\binom n2-k\le Cn$ and $n$ is sufficiently large. For example $G(3)=256/27<10.27$, below the published growth lower bound. The intervening inversion counts are still open. [Growth lower bound](https://arxiv.org/abs/1711.10325) · [Original conjecture](https://arxiv.org/abs/1111.5736)
