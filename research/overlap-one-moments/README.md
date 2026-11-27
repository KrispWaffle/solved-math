# Overlap-one packing moments

## Target and opening search, 27 November 2026

For every permutation $p$ of length $K\ge2$, let $N(j)$ count permutations on $1+j(K-1)$ positions whose $j$ prescribed windows have pattern $p$ and start $K-1$ positions apart. Additional occurrences are allowed. Conjecture 10.6 asserts that there is a positive probability measure on $[0,\infty)$ whose $r$th moment equals $N(r+1)$ for every $r\ge0$. The measure may depend on the pattern. This is a general positivity question for the order-polytope volumes of arbitrarily long tree posets after their factorial normalization. [Blitvić, Kammoun, and Steingrímsson, Part II, v1, §10](https://arxiv.org/html/2611.12829v1#S10)

A construction of that measure for all patterns would settle the conjecture. So would a proof of positive semidefiniteness of both the ordinary and shifted Hankel matrices at every order. An exactly negative quadratic form for one eligible pattern would refute the universal claim. The authors prove endpoint differences one and two and the extremal endpoint cases. Their counterexample to the earlier conjecture allowing arbitrary overlaps has a different overlap. [Part II, §§5, 8 and 10](https://arxiv.org/html/2611.12829v1)

I checked the paper, its OpenAlex citing record, searches for the title, the theorem number, overlap-one counts, tree-poset volumes, Stieltjes measures and Hankel total positivity, the local Mathlib sources, and the local and reference catalogues and issue discussions. OpenAlex listed zero citing works. One group developed a signed exact recurrence and checked leading minors for 294 endpoint triples. Another identified available total-positivity theorems and the missing representation of the raw packing counts. Both reported the full conjecture unresolved. These searches found no earlier proof or disproof. [Citation record](https://api.openalex.org/works?filter=cites:W7225712590&select=title,doi) · [Exact recurrence and checks](https://github.com/1337isnot1337/solved-conjectures/issues/161) · [Independent research record](https://github.com/the-omega-institute/trureturing/issues/28848)

## Approach

After orienting the endpoints in increasing order, write $a=p_1-1$, $c=p_K-p_1$ and $b=K-p_K$. The paper's trunk integral keeps every shared position in order and integrates out the pendant chains. I will try to recover the factorial in the raw counts by integrating the interval length against an exponential density. This turns successive trunk gaps into independent gamma variables. The question is then whether the resulting products at every occurrence count can be represented by powers of one positive variable or a positive operator. A second approach is to glue two stacks along one window and compute all Hankel entries from their boundary data.

## Progress

The exponential change of scale yields a positive formula for the raw counts in terms of independent gamma gaps with fixed shape parameters. A separate construction gives a row- and column-finite matrix of nonnegative integers whose return counts are exactly $N(r+1)$. This proves a renewal decomposition at every order. Two explicit transfer minors have opposite signs under every common reordering, so the total-nonnegativity criterion cannot be applied to this particular matrix. A general proof of the Hankel inequalities or a counterexample to the conjecture remains outstanding. [Gamma representation](GAMMA.md) · [Return matrix and obstruction](TRANSFER.md) · [Exact checks](transfer.py)

### Formal scope

Lean proves the return-matrix identity for the exact endpoint recurrence at all lengths, nonnegativity of every matrix entry for all parameters, and the obstruction to any simultaneous enumeration that would make the transfer totally nonnegative. The combinatorial identification of the endpoint recurrence with permutations and the gamma formula are written arguments. The Python check compares the original physical-position counts and endpoint counts in 608 instances, then tests return entries and exact transfer minors. [Lean source](Transfer.lean) · [Written identification](TRANSFER.md) · [Exact verifier](transfer.py)

Run the research checks from the repository root with

```sh
python3 research/overlap-one-moments/transfer.py
(cd lean && lake env lean -DwarningAsError=true ../research/overlap-one-moments/Transfer.lean)
```
