# The five tertiary generating functions

For the pair $1324,p$, let $s_d$ denote the eventual slope of $a(n+1,n+d)-a(n,n+d)$ and put $T_p(q)=\sum_{d\ge-1}s_dq^{d+1}$. Let $C_p(q)$ denote the ordinary stable inversion series of the same pair. Write $P(q)=\prod_{j\ge1}(1-q^j)^{-1}$ for ordinary partitions and $Q(q)=\prod_{j\ge1}(1+q^j)$ for partitions into distinct parts.

**Theorem.** The five strictly tertiary series are

| Partner $p$ | $T_p(q)$ |
|---|---|
| 2143 | $-2$ |
| 2413 | $3P(q)^2=3C_{2413}(q)$ |
| 2431 | $qC_{2431}(q)$ |
| 3412 | $2qC_{3412}(q)$ |
| 4231 | $2q^2Q(q)^2$ |

The four authors’ April preprint and Paper B of Verkama’s thesis recorded the negative constant followed by zeros for 2143, proposed the three identities involving $C_p$, and listed eight unexplained coefficients for 4231. The last row counts ordered pairs of distinct-part partitions after a shift of two and a factor of two. Its coefficients begin $0,0,2,4,6,12,18,28$. All five identities hold at every coefficient. [April preprint, §§5.3–5.5](https://arxiv.org/pdf/2604.01143v1) · [Corrected difference convention, v2 §5.2](https://arxiv.org/html/2604.01143v2#S5.SS2) · [Thesis, Paper B, §§5.3–5.5](https://diva-portal.org/smash/get/diva2%3A2050045/FULLTEXT01.pdf) · [Classifications of the primary series, Theorem 5.6 in the PDF](https://arxiv.org/pdf/2604.01143v2#page=18)

## Which decorations contribute?

Use the four oriented pairs of templates $D,J_t$ from the [classification proof](CLASSIFICATION.md). Their end decorations are $\gamma$ and $\delta$, where $\gamma$ avoids 132 and $\delta$ avoids 213. Each is either empty or a nontrivial indecomposable permutation. Put $w=\operatorname{inv}(\gamma)+\operatorname{inv}(\delta)$. Let $A_D,A_t$ be the indicators that the corresponding template avoids the oriented partner. The contribution of this decorated choice is

```math
q^w(1-q)\sum_{t\ge0}q^t(A_D-A_t).
```

Use the names “first–last” and “first–maximum” for the two displayed position/value templates in the classification proof. Their other two orientations are obtained by inverse and reverse-complement, respectively. The following table gives all nonzero indicator differences. Each line holds pointwise for arbitrary permissible end decorations.

| Partner | Orientations | Condition on the end decorations | $A_D-A_t$ when the condition holds |
|---|---|---|---|
| 2143 | first–last and its inverse | Both decorations avoid 21 | $-1$ for every $t$ |
| 2413 | inverse of first–last and both first–maximum orientations | Unrestricted | $1$ for every $t$ |
| 2431 | inverse of first–last | $\delta$ avoids 4132 | $1$ for $t\ge1$ |
| 3412 | both first–maximum orientations | Both decorations avoid 3412 | $1$ for $t\ge1$ |
| 4231 | first–last and its inverse | $\gamma$ avoids 231 and $\delta$ avoids 312 | $1$ for $t\ge2$ |

All other entries are zero. For example, in the normalized first–last template, an occurrence of 4231 can use both crossing roots as its four and one exactly when the intervening increasing block supplies a two and a three. This needs two intervening entries. In the decomposable template, an occurrence is possible precisely when $\gamma$ contains 231 or $\delta$ contains 312. It then occurs on both sides.

Here is a finite proof of every entry of the indicator table. For the positive lines verify that $D$ contains the partner exactly when one of the indicated core restrictions fails. For $t$ below the indicated threshold verify equality of occurrence in $D,J_t$. For $t$ at or above the threshold, $J_t$ already contains the partner with both decorations empty. For the negative line verify that $D$ always contains 2143, while $J_t$ contains 2143 exactly when either decoration contains 21. For omitted orientations verify equality of occurrence. Each comparison is an equivalence of occurrence conditions. A true side has a witness using at most four total entries of the decorations, and every witness lifts under reinstatement of the deleted entries. Consequently the equivalences need only the 64 pairs of witness patterns of total length at most four. Each straight interval can be clipped at four, so $t=0,1,2,3,4$ covers all possibilities. The checker exhausts precisely these witnesses and tests the conditions as stated. [Exact table verification](verify.py)

## Summing the table

For a threshold $r$, the factor $(1-q)\sum_{t\ge r}q^t$ is $q^r$. A decoration avoiding 21 can only be empty: a nontrivial increasing permutation is decomposable. Thus the two negative choices give the constant $-2$.

The inversion series of the empty or nontrivial indecomposable 132-avoiding decorations is $P(q)$, as is its 213 counterpart. This counts the zero coefficient once by the empty decoration in place of the singleton. For 2413 there are three copies of the unrestricted ordered pair, giving $3P(q)^2$.

For 2431, inversion is a weight-preserving bijection between 213-avoiding decorations avoiding 4132 and those avoiding 2431. The left decoration is unrestricted. The product of these two core series is $C_{2431}(q)$ by the known decomposition of the primary limit. For 3412 each core has the corresponding 3412 restriction, so the product is $C_{3412}(q)$. The thresholds and multiplicities give $qC_{2431}(q)$ and $2qC_{3412}(q)$. [Decomposition and primary series, Corollary 5.5 and Theorem 5.6 in the PDF](https://arxiv.org/pdf/2604.01143v2#page=17)

Franklín’s Theorem 18 gives the distinct-part bijection for an individual 132- and 231-avoiding indecomposable end. Here the tertiary formula calls for its two independent copies. For 4231, reverse-complement identifies the right decorations avoiding 213 and 312 with the left ones avoiding 132 and 231. A permutation avoiding 132 and 231 decreases up to its minimum and increases thereafter. In fact both forbidden patterns are exactly the three-letter orders having a peak in the middle. The entries to the left of the minimum can therefore be any subset of $\{2,\ldots,n\}$ listed in decreasing order. Each such entry $b$ contributes exactly $b-1$ inversions. A nonsingleton of this form is indecomposable precisely when $n$ lies to the left of the minimum: it then starts with $n$, whereas the other possibility ends with $n$. Consequently the decoration is encoded by the finite subset of positive integers $b-1$ used on the left. Every nonempty finite subset gives exactly one length, namely one plus its largest member. The empty decoration accounts for the empty subset. Each end thus has series $Q(q)$. The last line of the indicator table gives $2q^2Q(q)^2$. ∎ [Franklín, Theorem 18](https://arxiv.org/pdf/2410.07467v4#page=17)
