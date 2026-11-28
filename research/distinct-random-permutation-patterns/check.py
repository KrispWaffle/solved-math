"""Exact small-order checks of the embedding classes and fixed-gap bound."""

from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, factorial


def pattern(permutation, positions):
    values = [permutation[x] for x in sorted(positions)]
    ranks = {value: rank for rank, value in enumerate(sorted(values))}
    return tuple(ranks[value] for value in values)


def between(a, x, b):
    return min(a, b) < x < max(a, b)


def local_pairs(permutation, red, labels):
    return [
        (a, b) for a in red for b in labels - red
        if all(not between(a, x, b) and not between(permutation[a], permutation[x], permutation[b])
               for x in red - {a})
    ]


def separated(permutation, pairs):
    for (a, b), (c, d) in combinations(pairs, 2):
        if len({a, b, c, d}) < 4:
            return False
        for x, y, z, w in ((a, b, c, d), (permutation[a], permutation[b], permutation[c], permutation[d])):
            if max(min(x, y), min(z, w)) <= min(max(x, y), max(z, w)):
                return False
    return True


def check_classes(max_n):
    subsets_checked = 0
    for n in range(1, max_n + 1):
        labels = frozenset(range(n))
        subsets = [frozenset(s) for r in range(n + 1) for s in combinations(range(n), r)]
        pair_totals = Counter()
        for permutation in permutations(range(n)):
            classes = defaultdict(set)
            for red in subsets:
                classes[pattern(permutation, red)].add(red)
            reciprocal_sum = Fraction(0)
            for group in classes.values():
                for red in group:
                    reciprocal_sum += Fraction(1, len(group))
                    pairs = local_pairs(permutation, red, labels)
                    pair_totals[len(red)] += len(pairs)
                    if separated(permutation, pairs):
                        images = {red}
                        for a, b in pairs:
                            images.update((s - {a}) | {b} for s in tuple(images))
                        assert len(images) == 2 ** len(pairs)
                        assert images <= group
                    subsets_checked += 1
            assert reciprocal_sum == len(classes)
        for m in range(n + 1):
            expected = Fraction(4 * m * (n - m), (m + 1) ** 2)
            assert pair_totals[m] == expected * factorial(n) * comb(n, m)
    return subsets_checked


def check_slot_bounds():
    """Count one-order isomorphisms for labelled paths with arbitrary fixed vertices."""
    checked = 0
    for lengths in ((1,), (2,), (3,), (1, 1), (2, 1), (2, 2), (3, 1), (1, 1, 1)):
        b, moved = len(lengths), sum(lengths)
        for fixed in range(9 - moved - b):
            domain = list(range(fixed))
            mapping = {x: x for x in domain}
            start = fixed
            for length in lengths:
                for x in range(start, start + length):
                    domain.append(x)
                    mapping[x] = x + 1
                start += length + 1
            total = 0
            for order in permutations(range(start)):
                ranks = {x: j for j, x in enumerate(order)}
                tails = sorted(domain, key=ranks.__getitem__)
                heads = [ranks[mapping[x]] for x in tails]
                total += heads == sorted(heads)
            edge_matching = sum((length + 1) // 2 for length in lengths)
            upper = Fraction(comb(fixed+b, b), factorial(edge_matching)*comb(start, moved+b))
            assert Fraction(total, factorial(start)) <= upper
            checked += 1
    return checked


if __name__ == "__main__":
    # The pointwise condition matters even when the two resulting unlabelled patterns coincide.
    monotone = (0, 1, 2)
    assert pattern(monotone, {0, 1}) == pattern(monotone, {1, 2})
    assert (0, 2) not in local_pairs(monotone, frozenset({0, 1}), frozenset(range(3)))
    print(f"Checked {check_classes(6)} colored permutation instances and {check_slot_bounds()} path bounds.")
