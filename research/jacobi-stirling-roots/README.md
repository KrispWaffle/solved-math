# Real roots of the Jacobi–Stirling descent polynomials

## Target and opening search, 27 November 2026

Gessel, Lin, and Zeng ask in Conjecture 15 that $A_{k,i}(t)$ have only real roots for every $k\ge0$ and $0\le i\le k$. Their polynomial is the numerator of the ordinary generating series in $n$ for the coefficient of $z^i$ in the Jacobi–Stirling number $\mathrm{JS}(n+k,n;z)$, with denominator $(1-t)^{3k-i+1}$. For $k>0$ the permutation version using only internal descents removes one factor of $t$. A proof for every pair or one valid nonreal zero settles the conjecture. A proof for another fixed deletion size would leave the general assertion open. This is a fourteen-year-old question about the effect of summing many real-rooted descent polynomials, which in general can destroy real-rootedness. [Original Conjecture 15, v2](https://arxiv.org/pdf/1201.0622v2) · [Published version](https://doi.org/10.1016/j.ejc.2012.06.008)

The original paper obtains the endpoint cases and real-rootedness for each fixed deletion set. Ma and Wang prove five further infinite families, leaving the middle deletion range unresolved. I searched the primary paper, its title, authors, conjecture number, recent partial proof, real-rootedness and counterexample variants, Mathlib, and the local and public research catalogues. The public accounts report the equal-weight sum unresolved. There is an explicit obstruction to the stronger arbitrary-positive-weights assertion. It concerns a different weighting. The separate result on Zhu's Jacobi–Stirling Hankel matrices has a different polynomial and target. [Ma–Wang, Theorem 2](https://arxiv.org/abs/2610.03111) · [Source-matched issue](https://github.com/the-omega-institute/trureturing/issues/20313) · [Research notes and obstacles](https://github.com/1337isnot1337/solved-conjectures/issues/84) · [Zhu's distinct problem](https://github.com/1337isnot1337/solved-conjectures/issues/430)

## Approach

I will use the known recurrence for the equal-weight aggregate and look for an interlacing criterion that survives insertion. The common-interlacer approach for arbitrary weights fails. The coefficient sequence with exactly $i$ deletions retains more structure. Comparing consecutive aggregate deletion polynomials, or proving a real-variable inequality only on the interval containing their zeros, could control the sum at the next insertion.

## Research checkpoint

A determinant identity shows that a Turán inequality on $(-1,0)$ for each aggregate row would imply strict interlacing at the next row and would settle the full conjecture. The written argument also controls zeros under a continuous deletion weight. Independently, a canonical way of reinserting missing bars expresses all deletion rows in terms of adjacent bars in full words. The general Turán sign remains open. [Reduction and proof](REDUCTION.md) · [Bar reinsertion formula](BONDS.md)

Lean checks the polynomial determinant identity, its strict sign at each prescribed next root under the displayed hypotheses, and removal of the common padding factor. The interlacing induction and bar bijection are written arguments. The direct checker compares every coefficient from the actual words, their insertion recurrence, and the bar formula for $0\le k\le4$. [Lean source](Reduction.lean) · [Combinatorial checker](check.py)

Run `python3 research/jacobi-stirling-roots/check.py` from the repository root. The research Lean file uses Lean 4.36.0 and Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. In a Lake project with that dependency built, run `lake env lean -DwarningAsError=true /path/to/solved-math/research/jacobi-stirling-roots/Reduction.lean`. [Pinned Mathlib](https://github.com/leanprover-community/mathlib4/tree/fc4f59e577feb1a4956671bc04ac18aaaf8cd842)
