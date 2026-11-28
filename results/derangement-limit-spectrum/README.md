# Attainable limiting proportions of derangements in permutation classes

**Every real number from zero to one occurs.** For each prescribed value, one infinite permutation class has that limiting fraction of fixed-point-free members along all positive lengths. The class can have growth rate between $5/2$ and $13/5$. [Complete proof](PROOF.md) · [Independent review](AUDIT.md)

## Original target

Immediately after Question 4.3, Vatter asks which numbers in $[0,1]$ occur as limiting proportions of derangements in infinite permutation classes. A class is a set closed under taking classical patterns. At each length its members have equal weight. A derangement has no fixed position. The question asks for the set of actual limits along all positive lengths, allowing the class to depend on the desired limit. A characterization covering irrational numbers would answer the question beyond the known examples. [Vatter, published version, §4, p. 18](https://arxiv.org/pdf/2602.16355v4#page=18)

## Opening search, 28 November 2026

Vatter’s final update credits Wenlin Zhang and Haobo Ma with a family whose limits are $k/(k+1)$ approaching one. The decreasing class alternates between zero and one, and several pattern-avoidance classes have individual computed limits. These results answer different parts of §4. The published source’s attainable-values question remains after incorporating these examples. The public formalization of cofinality explicitly distinguishes its theorem from the classification of all attainable values. [Published update, p. 32](https://arxiv.org/pdf/2602.16355v4#page=32) · [Cofinality theorem and scope](https://the-omega-institute.github.io/trureturing-mdbook/Problems/vatter-largest-derangement-limit-below-one.html)

Searches for attainable derangement proportions, derangement-limit spectrum, fixed-point-free densities, rational and real limiting probabilities, and small permutation classes located results on a different logic of permutations and on the growth-rate spectrum. The reference catalogue’s main and research trees, issues and PR records, this repository’s branches and pinned Mathlib yielded no entry establishing this exact attainable-limit classification. The separately published solution for separable derangements concerns one class. The search is bounded, and a second search and independent review are required before promotion. [First-order limiting probabilities](https://arxiv.org/abs/2610.34328) · [Growth rates of permutation classes](https://arxiv.org/abs/0807.2815) · [Separable derangements](https://github.com/1337isnot1337/solved-conjectures/pull/443)

## Polynomial-growth classes

The even and odd derangement proportions each have a rational limit. A finite calculation decides whether they agree. Every rational in $[0,1]$ occurs in this family. Lean gives actual hereditary witnesses with exact counts for every rational. The fraction of fixed points also has a limit along all lengths, described by a finite mixture of beta distributions and point masses. [Classification and proof](POLYNOMIAL-CLASSES.md) · [Rational witnesses in Lean](../../lean/SolvedMath/DerangementRationals.lean)

## Prescribing the growth rate

For any growth rate at least Bevan's constant (about 2.357), every limiting derangement proportion in $[0,1]$ occurs at that exact rate. The construction also gives sum-closed classes at every rate on the upper ray of Vatter's Conjecture 10.1. The interval between the two known growth thresholds remains open for that conjecture. [Proof and scope](PRESCRIBED-GROWTH.md) · [Lean displacement and series lemmas](../../lean/SolvedMath/DerangementGrowth.lean)

## Construction and verification

A skew sum of two typical long members of the chosen sum-closed class moves both blocks far enough to avoid fixed points. A finite suffix then determines the limiting proportion through its length-weighted count of derangements. Two finite truncations, combined into one hereditary suffix class, place the target between the ratios at the two ends of a growth-rate interval. Continuity gives the desired class. [Proof](PROOF.md)

Lean proves that derangement of a direct sum is equivalent to derangement of both factors, how a skew sum shifts displacements, and how the first direct cut recovers an indecomposable prefix. It verifies two hereditary classes attaining zero and one, including the exact count of deranged cyclic shifts at every positive length. It proves the full source statement assuming the two written estimates on finite decorations. The construction and asymptotic estimates for the interior values have a reviewed written proof. [Finite sums and cuts](../../lean/SolvedMath/DerangementSpectrum.lean) · [Endpoints and exact source statement](../../lean/SolvedMath/DerangementEndpoints.lean)

Run `./scripts/verify.sh` from the repository root. The per-result checker also runs independently with `python3 results/derangement-limit-spectrum/verify.py`. [Exact checker](verify.py)
