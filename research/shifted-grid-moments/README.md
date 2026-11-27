# Shifted-grid packing moments

## Target and eligibility, 27 November 2026

Conjecture 10.5 of Blitvić, Kammoun and Steingrímsson asks for one positive probability measure on the nonnegative real axis for each eligible permutation and overlap. Its moment of order $r$ must equal the number of permutations with $r+1$ prescribed regularly spaced occurrences, for every $r\ge0$. For a pattern of length $K$ the overlap satisfies $2\le m\le K/2$. Its first and last $m$ positions have the same relative order. Their sorted values satisfy $1=p_1<s_1<p_2<s_2<\cdots<p_m<s_m=K$. The conjecture allows every horizontal and vertical subdivision compatible with these inequalities. A full representing measure, a proof of positivity of both complete Hankel forms for each family, or a single rigorously negative Hankel form in an eligible family would settle the question. [Primary source, v1, §§7 and 10](https://arxiv.org/html/2611.12829v1#S10)

The authors prove the two-level case with arbitrary subdivisions, and the three-level unsubdivided case. The earlier unrestricted conjecture has a counterexample outside the shifted-grid hypotheses. I searched the source identifier, exact conjecture number, shifted and truncated strips, Stieltjes and Hausdorff moments, Hankel obstructions, Mathlib and the two public research collections. The most specific external study records nonnegative return counts, growth estimates and some corner minors. It ended with the full assertion unresolved. Its upper growth bound for families without vertical subdivisions already gives the natural endpoint for the Hausdorff moment question. [External study and its scope](https://github.com/the-omega-institute/trureturing/issues/29090) · [Earlier permutation-packing catalog](https://github.com/1337isnot1337/solved-conjectures/tree/main/results/blitvic-kammoun-steingrimsson-packing-cutoff)

## Partial results

| Grid held fixed or varied | Hankel test | Argument |
| --- | --- | --- |
| Any fixed grid with a vertical subdivision | Every fixed minor becomes positive when all indices are dilated sufficiently far. | The counts have a two-term logarithmic expansion. Its linear coefficient is a quantile-entropy variational problem. [Proof](FIXED-GRID.md) |
| Fixed unsubdivided grid, arbitrary height | Every fixed minor becomes positive after a sufficiently large common translation of its moment indices. | A reflection determinant for the middle of a tableau gives a full asymptotic series and the positive leading constant of each translated minor. [Proof](TRANSLATED-MINORS.md) |
| Unsubdivided grids of increasing height | Every fixed minor is eventually positive, with exponential decay of the relative error from its diagonal product. | The logarithmic growth rate from the open exclusion process is strictly convex. [Proof](LARGE-HEIGHT.md) |
| Arbitrary periodic profiles of horizontal and vertical subdivisions | Every sufficiently large fixed dilation gives positive minors at all sufficiently large heights. | A finite transfer retains the boundary of the original grid. A subadditivity argument controls its period growth rates. [Proof and transfer](PERIODIC-GRIDS.md) |

The original conjecture requires every minor at each prescribed grid and index set. These theorems leave that assertion open. The large-height proof constructs the tableau–walk correspondence directly in BKS coordinates. It explains a coordinate discrepancy in Dal Zovo’s v1 and uses the published open-boundary free-fermion spectrum. Earlier tableau recurrences also treat the ordinary strip counts. [Dal Zovo, Theorem 1](https://arxiv.org/html/2605.29520v1#S3) · [Nakerst, Prosen and Haque, §IV](https://arxiv.org/html/2402.00662#S4) · [Sun](https://arxiv.org/abs/1506.07256) · [Chan](https://doi.org/10.1016/j.ejc.2022.103599)

## Local verification

Run `./research/shifted-grid-moments/verify.sh` from the repository root. Lean proves the strip growth-rate curvature, determinant dominance from strict four-point inequalities, eventual positivity from the displayed entrywise strip growth, and positivity of dilated minors from the two-term factorial growth expansion with positive coefficient. The tableau correspondence, spectral calculation, entropy formula, full fixed-height expansion and periodic rate argument are written mathematics. [Lean declarations](FixedMinors.lean)

The exact checks compare 70 original packing counts to exclusion walks, 130 subdivided grids to the periodic transfer, six chamber determinants to direct walks and six row-integral expansions to physical-position counts. [Counting checks](check.py) · [Periodic transfer and rational growth bounds](periodic.py)
