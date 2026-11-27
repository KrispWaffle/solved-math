# Repeating subdivisions in the height direction

Choose any period $p\ge1$ of horizontal counts $h_1,\ldots,h_p$ and vertical counts $v_1,\ldots,v_p$, all nonnegative. At height $m$, use the first $m$ horizontal levels and the first $m-1$ vertical links of this repeated profile. Write $N_m(j)$ for the actual count with $j\ge1$ prescribed windows. Define

```math
C=p+\sum_{i=1}^p(h_i+v_i),\qquad D_j=Cj+p .
```

The following gives an explicit integer transfer for the entire profile. General finite transfers for periodic tableaux and the unsubdivided exclusion-process correspondence are precedents. The shared events below retain vertical and horizontal subdivisions and the terminal boundary of the packing. [Source grid, §7.1](https://arxiv.org/html/2611.12829v1#S7) · [Periodic P-partitions](https://www.sciencedirect.com/science/article/abs/pii/S0195669822000956) · [Dal Zovo, Theorem 1](https://arxiv.org/html/2605.29520v1#S3)

## The transfer

Use one cyclic list of events for each window. At each successive level its list consists of a left checkpoint, $h_i$ private events, a right checkpoint, and $v_i$ private events. The last level of the period is followed by the first. A state gives the next event of each of the $j$ lists. Initially all wait at the left checkpoint of the first level. A private event advances its own list. An outside checkpoint advances the corresponding end list. An interior right checkpoint advances its list and the next list together precisely when the latter waits at the left checkpoint of the same level. Let $T_j$ be the adjacency matrix on the states reachable from the initial state; count all edges with their multiplicities.

Each walk lifts to the infinite list in every window. For interior neighbors the number of right checkpoints consumed on the left equals the number of left checkpoints consumed on the right, since each is consumed by their common event. In particular the periodic implementation matches their absolute level numbers, starting from level one. A legal labeled move is precisely the next available element of the union of window chains. For the original height $m$, stop with every list immediately after its last right checkpoint, before any final vertical event. At these terminal phases the lifted number of levels completed by adjacent windows agrees: both have consumed equal numbers of left and right checkpoints within their own windows, in addition to equality across the common checkpoint. The length $m+j(m+\sum_{i\le m}h_i+\sum_{i<m}v_i)$ singles out the desired lift. This proves that the designated matrix entry counts every physical linear extension once. It also explains why inserting the last group of vertical events would change the enumeration.

Every reachable state can be extended back to the initial phases at the end of a sufficiently late period. Its lifted walk is a finite order ideal. Choose a period boundary beyond all completed events, include the private vertical events following its last right checkpoint, and extend the ideal in any topological order of this finite collection. The added final private events in each list follow its last right checkpoint and precede the next period. Thus the reachable graph is irreducible. At a return all windows have completed equally many entire periods; one period contributes $D_j$ distinct moves. A single period can indeed be traversed, so the period of the graph is exactly $D_j$. Perron–Frobenius on a cyclic class gives a positive exponential rate per period,

```math
\Lambda_j=\rho(T_j)^{D_j},\qquad
\lim_{n\to\infty}\frac{\log N_{np+r}(j)}n=\log\Lambda_j
\quad(0\le r<p).
```

For a fixed terminal residue choose any one path to it. Paths with successively one further period start in the same cyclic class, where the $D_j$-step matrix is primitive. The corresponding terminal column is nonnegative and accessible, giving the same rate. The [exact implementation](periodic.py) also gives rational upper and lower bounds using the largest and smallest coordinate ratios of consecutive powers of that primitive block applied to the all-ones vector.

## Growth of the period rates in the number of windows

There is a finite real number $e$ depending only on the profile such that

```math
\log\Lambda_j=Cj\log j+ej+o(j)\qquad(j\to\infty).
```

For an upper bound every state has at most $j$ outgoing moves, giving $\log\Lambda_j\le D_j\log j$. For a lower bound choose $H=1+\max_i h_i$ and integers $t_1=0$, $t_{i+1}-t_i=H+v_i+1$ on the repeated levels. Give checkpoint $u_{i,q}$ time $t_i+Hq$. Between horizontal checkpoints put their $h_i$ private events at distinct increasing integer times immediately after the earlier checkpoint. Put vertical private events at the successive intervening integer times. All defining comparisons now strictly increase time. The schedule repeats, translated by $P=\sum_{i=1}^p(H+v_i+1)$, every period in height. In any full time period away from the two ends of the finite strip, the layer sizes $k_1,\ldots,k_P$ are fixed and sum to $D_j$: in the doubly infinite strip each orbit of a distinct event under height translation has exactly one time in any block of $P$ consecutive times. At fixed $j$ only $O_j(1)$ end periods are affected, since the horizontal displacement spans at most $Hj$. Within each time layer one may permute events freely. Thus $\Lambda_j\ge\prod_t k_t!\ge D_j!/P^{D_j}$ by the multinomial theorem. In particular $\log\Lambda_j-Cj\log j$ is bounded above and below by linear functions of $j$.

To obtain the linear coefficient, delete the $m$ final-column checkpoints $u_{i,j}$ from a $j$-window grid and give the remaining vertices the induced order. Let $B_m(j)$ count its extensions. The deleted checkpoints form a chain through the last window. Every extension of an induced subposet extends to the full poset: imposing its ordering creates no directed cycle, since any segment through the other vertices already imposes an induced comparison. The deleted chain can occupy at most $\binom{m+jd_m}{m}$ sets of slots, where $d_m=m+\sum_{i\le m}h_i+\sum_{i<m}v_i$. Hence

```math
B_m(j)\le N_m(j)\le\binom{m+jd_m}{m}B_m(j).
```

Assign checkpoint column $q$ and the private events of window $q+1$ to block $q$, $0\le q<j$. Cutting between blocks partitions the half-open strip into disjoint sets of $j d_m$ and $k d_m$ vertices. Their induced orders contain all relations in the corresponding smaller half-open strips, since the full chains witnessing those relations also occur in the larger grid. Restricting an extension to the two portions and recording the shuffle gives

```math
B_m(j+k)\le\binom{(j+k)d_m}{jd_m} B_m(j)B_m(k).
```

At $m=np$, $d_{np}=nC-v_p$. Define $b_j=\limsup_n n^{-1}\log B_{np}(j)-Cj\log j$. Stirling's formula in the last inequality gives $b_{j+k}\le b_j+b_k$. At fixed $j$, the preceding slot bound costs at most
$(Cj+p)\log(Cj+p)-Cj\log(Cj)-p\log p=O(\log(j+1))$ per period. Consequently $b_j$ has a linear lower bound by the schedule estimate. Fekete's lemma gives the finite limit $e=\lim_j b_j/j$; the slot error divided by $j$ tends to zero. This proves the expansion.

## Hankel consequence for every periodic subdivision profile

Fix any two strictly increasing lists of nonnegative integer indices $a_i,b_l$. For every sufficiently large integer dilation $s$, the minor with entries $N_m(s(a_i+b_l)+1)$ is positive for all sufficiently large heights $m$. The height threshold may depend on $s$. For each fixed $z\ge0$ the expansion gives

```math
s^{-1}\log\Lambda_{sz+1}-Cz\log s-ez\longrightarrow Cz\log z,
\qquad 0\log0=0.
```

For $z=0$ use $\Lambda_1=1$. The first two subtracted terms add to the same quantity in every permutation of the determinant. Strict convexity of $z\log z$ gives a limiting gap in favor of the identity permutation at every inversion, including at the endpoint zero. There are finitely many competing terms; for sufficiently large $s$ the original rate sums are already strictly ordered below the diagonal one. For each such $s$, take the height to infinity. The period rate gives exponential decay of every nondiagonal product relative to the diagonal product on each residue class. Taking the maximum threshold over the finitely many residues proves the assertion. This result also covers horizontal subdivisions of positive length with all vertical counts zero.
