# Separator theorem audit

## Problem and scope

Blitvić, Kammoun, and Steingrímsson ask for a characterization of pattern posets with a separator. In the same item they propose that position $K$ always works for overlap two under explicit inequalities on the prefix and suffix. The Lean theorem proves that entire proposed family for all pattern lengths, all middle orders, and every $j>2$. The arbitrary-overlap theorem gives a sufficient condition for the broader question. A necessary and sufficient characterization for all patterns is outside these conclusions. [Part I, §7, item 5](https://arxiv.org/html/2610.29846v1#S7)

## Correspondence with the paper

| Source object | Representation in Lean |
|---|---|
| Permutation of length $K$ | A rank function that restricts to a bijection on the first $K$ natural numbers. Ranks at other positions never enter window comparisons. |
| Position in the stack | A physical integer position $dt+i$, with $t<j$, $i<K$, and $d=K-m$. The same integer in two windows is the same vertex. |
| Strict order | The inductive relation Below contains each within-window rank comparison and is closed under transitivity. The height proof establishes irreflexivity for the theorem’s family. |
| Separator | The vertex compares with every vertex. The strict lower and upper sets each contain a pair of distinct positions with neither direction of Below. |
| Paper’s label $K$ | Zero-based physical position $K-1$. The final theorem accepts $a,b,c$ and the inequalities in their one-based source notation. |

The general declaration is SeparatedOverlap.separator. The source-facing corollary bks_overlap_two_separator constructs all its hypotheses from the four endpoint ranks and the paper’s inequalities. Lean’s kernel reports only propositional extensionality and quotient soundness for both declarations. The project checks these reports when it builds. [Lean source](../../lean/SolvedMath/PatternSeparator.lean) · [Axiom check](../../lean/ProofAudit.lean) · [Original order definition](https://arxiv.org/html/2610.29846v1#S5)

## Prior-work search on November 27, 2026

- The original paper gives related cycle and chain criteria in Theorems 5.20 and 5.23 and returns to the separator assertion in its open-problems section. The authors’ Part II treats enumeration and moment sequences. Its section on separated occurrences concerns disjoint windows. [Part I](https://arxiv.org/html/2610.29846v1#S5) · [Part II, §5.2](https://arxiv.org/html/2611.12829v1#S5.SS2)
- OpenAlex’s citing-work list for Part I returned Part II and Zoltán Nagy’s paper. Nagy proves the uniform double-factorial construction requested in item 6. [OpenAlex record](https://api.openalex.org/works?filter=cites:W7223210855&select=title,doi) · [Nagy’s paper](https://arxiv.org/abs/2611.06937)
- Searches used the authors’ names, the arXiv identifier, “separator”, “pattern-packing poset” and “overlap two”. I checked the reference repository’s result directories and issue discussions, including its result on item 8. A separate public discussion explicitly identifies item 5 as an unfinished lead. I found no earlier proof of the separator assertion in the sources searched. [Reference repository](https://github.com/1337isnot1337/solved-conjectures) · [Item 5 research discussion](https://github.com/the-omega-institute/trureturing/issues/28504#issuecomment-6746309804)

## Direct check

The Python verifier creates the adjacent-rank inequalities in each actual window and takes their transitive closure. It tests comparability with $K$ and looks for incomparable pairs in both sides without using the height formula. It checked 2,592 posets with overlaps two through four, including 276 cases satisfying the paper’s stricter endpoint conditions. As a check on the interpretation of “separator”, the verifier reproduces both examples in item 5. It finds three separators for 135268479 at overlap three and five for 479258136 at overlap six. It also rejects a chain and a two-window example whose upper side is a chain. [Verifier](verify.py)
