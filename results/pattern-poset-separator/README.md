# Separators in permutation-pattern posets

Blitvić, Kammoun, and Steingrímsson proposed that a specific position separates a poset built by overlapping copies of a permutation. A separator is comparable with every position, with an incomparable pair strictly below it and another strictly above it. [Part I, §7, item 5](https://arxiv.org/html/2610.29846v1#S7)

**Lean-verified theorem.** Suppose a length-$K$ permutation begins with $1,a$, ends with $b,c$, and $2<a<b<c-1<K-2$. In every stack of at least three occurrences overlapping in two positions, position $K$ of the first occurrence is a separator.

The same conclusion holds for any overlap size when the increasing prefix ranks all precede the increasing suffix ranks, the first rank is the minimum, and some pair of successive overlap positions has a gap on both lists. The interfix can have any ordering. The paper’s broader question of classifying all patterns with a separator remains open in this work.

[Written proof](PROOF.md) · [Lean theorem](../../lean/SolvedMath/PatternSeparator.lean) · [Statement and prior-work audit](AUDIT.md) · [Direct checker](verify.py)
