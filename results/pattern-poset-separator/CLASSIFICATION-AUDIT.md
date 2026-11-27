# Audit of the separator classification

## Target and opening search, 27 November 2026

For an arbitrary compatible permutation pattern and overlap, characterize when its packing poset has a separator for occurrence counts greater than the overlap. A full answer should determine the answer for each count and decide from the pattern and overlap whether it holds for every such count. A test that builds the entire poset anew for each count leaves the uniform question open. The published repository result proves only a sufficient condition on separated increasing boundary ranks. [Original question, Part I §7 item 5](https://arxiv.org/html/2610.29846v1#S7) · [Earlier sufficient condition](PROOF.md)

I searched by the authors, “pattern packing poset”, “separator”, “ordinal sum”, “characterization” and “arbitrary overlap”. Part II treats enumeration and moment sequences. The public item-5 discussion records the question as an unfinished lead. Neither gives the general classification. The existing local Lean proof requires the separated-boundary hypotheses. The opening search found no resolution in the sources examined. [Part II](https://arxiv.org/abs/2611.12829) · [Research discussion](https://github.com/the-omega-institute/trureturing/issues/28504#issuecomment-6746309804)

## Initial approach

A comparison carried from one window to the next must cross a shared position. Sort the shared positions by their ranks. Moving right, the least shared suffix rank at least as high as a starting rank carries the comparison to its paired prefix rank. Reversing the direction swaps prefix and suffix. The resulting maps preserve order on a finite chain, so their iterates eventually stabilize. The outstanding step at this point was to turn stabilization of pair comparisons into a uniform test for a separator with incomparable pairs on both sides.

## Correspondence and scope

The source asks an open question followed by a conjectural assertion for a special family. The general finite criterion and the earlier assertion share this result directory. For an arbitrary permutation, the final Lean declarations take exactly a positive proper overlap and the order equivalence of prefix and suffix. There is no bound on the size of the middle, the overlap, or the number of windows beyond the source hypotheses. The masks represent comparisons on physical positions even when a position has more than two representatives. The finite characterization gives existence at each count and a decision for all counts greater than the overlap. The cutoff bounds existence only. [Written proof](CLASSIFICATION.md) · [Source §2](https://arxiv.org/html/2610.29846v1#S2) · [Compatibility convention, §3](https://arxiv.org/html/2610.29846v1#S3) · [Poset, §5](https://arxiv.org/html/2610.29846v1#S5) · [Question, §7](https://arxiv.org/html/2610.29846v1#S7)

## Prepublication priority search, 27 November 2026

I repeated the search using the paper identifier, all three authors, and combinations of “pattern-packing poset”, “cluster poset”, “separator”, “ordinal sum”, “cutoff”, “rank”, “stabilization” and “overlap”. OpenAlex returned two citing papers. Part II develops moment sequences, and Nagy addresses item 6 on double factorials. The primary cluster-poset papers of Elizalde and Noy and of Lee and Sah analyze enumeration, avoidance and Wilf equivalence. The interval theory of Elizalde and McNamara concerns a different partial order on permutations. I found no earlier boundary-rank classification or stabilization result for packing-poset separator existence in these sources. [Citing works](https://api.openalex.org/works?filter=cites:W7223210855&select=title,doi) · [Part II](https://arxiv.org/abs/2611.12829) · [Nagy](https://arxiv.org/abs/2611.06937) · [Elizalde–Noy](https://doi.org/10.1016/j.aam.2012.08.003) · [Lee–Sah](https://doi.org/10.1016/j.aam.2018.10.001) · [Elizalde–McNamara](https://dmtcs.episciences.org/6380)

I checked the local Mathlib source, the fresh Solved Math catalogue at `bf94058`, and the reference collection's publication and research trees and issues. The matching Solved Math result proves a sufficient condition. The reference issues concern enumerative cutoffs and moments. The separate public item-5 discussion describes an unfinished lead. This is a bounded priority search as of the date above. [Reference catalogue](https://github.com/1337isnot1337/solved-conjectures) · [Enumerative cutoff issue](https://github.com/1337isnot1337/solved-conjectures/issues/374) · [Moment issue](https://github.com/1337isnot1337/solved-conjectures/issues/161) · [Item-5 discussion](https://github.com/the-omega-institute/trureturing/issues/28504#issuecomment-6746309804)

## Reproducible checks

The local verification command is `./scripts/verify.sh`. The Python checker compares the two transfer maps with the transitive closure of the actual window graph. It checks both directions of every slot comparison and the complete set of physical separator labels for 1,220 stacks, covering all permutations of lengths two through five, every admissible overlap, and one through five windows. Additional cases reproduce both examples in item 5 and compare existence beyond the cutoff. Evaluating the Lean Boolean decision on 2143 at overlap one returns true for two windows, false for three and false for the uniform question. [Graph checker](verify.py) · [Rank checker](classification.py) · [Checked declarations](../../lean/ProofAudit.lean)

Nanoda 0.4.17 independently type-checked 2,089 exported declarations with zero errors. The two main theorems use propositional extensionality, classical choice, and quotient soundness. From the pinned Lean package, the independent replay was run with

```bash
set -o pipefail
lake env leanexport SolvedMath.SeparatorClassification -- \
  SolvedMath.PatternSeparator.bks_separator_at \
  SolvedMath.PatternSeparator.bks_separator_always |
  lake env nanoda_bin <(echo '{"use_stdin":true,"permitted_axioms":["propext","Classical.choice","Quot.sound"],"unpermitted_axiom_hard_error":true,"nat_extension":true,"string_extension":true,"pp_to_stdout":true,"print_success_message":true}')
```

## Independent mathematical review, 27 November 2026

A separate Codex reviewer working in a fresh context read the original paper (§§2, 3, 5 and 7), the manuscript, the four Lean modules from the physical poset through the cutoff, and both source-facing declarations, `bks_separator_at` and `bks_separator_always`. The reviewer endorsed publication as a finite algorithmic characterization. Their review checked the treatment of multiple row representatives, paths that cross back and forth, nonchain witnesses, the inclusive cutoff, both endpoint overlap sizes, and the order of quantifiers. The separating position may depend on the count.

The reviewer requested two clarifications. The manuscript now describes the split as an ordinal sum, since a side may have more than one connected component. The long-overlap paragraph now distinguishes the local position of a label from its rank slot and gives the rank at the normalized position. Neither change altered a formal statement or proof.

An independent traversal by the reviewer returned separator labels 8, 14, 20 in the first source example and 8, 11, 14, 17, 20 in the second. It confirmed the example 2143 and agreed with the existence test on another 1,056 stacks, including 126 with overlaps longer than half the pattern. Repository verification separately passed the Lean build, fresh kernel replay, catalog tests, and all Python verifiers. [Written proof](CLASSIFICATION.md) · [Lean declarations](../../lean/SolvedMath/SeparatorClassification.lean)
