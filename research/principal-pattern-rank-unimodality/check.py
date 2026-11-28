"""Exact finite checks of slice curvature and the rank convention."""

from fractions import Fraction
from itertools import combinations
from math import comb


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def check_slice_curvature(max_n):
    checked = 0
    for n in range(2, max_n + 1):
        for b in range(n + 1):
            for m in range(n - 1):
                positive = Fraction()
                negative = Fraction()
                for j in range(b + 1):
                    # Probability of exactly one prescribed subset of the b labels.
                    p0, p1, p2 = (
                        Fraction(choose(n - b, k - j), comb(n, k))
                        for k in (m, m + 1, m + 2)
                    )
                    change = (p2 - 2 * p1 + p0) * comb(b, j)
                    positive += max(change, 0)
                    negative += min(change, 0)
                # Taking h=1 precisely on the positive coefficients attains this norm.
                assert positive == -negative
                assert positive <= Fraction(2 * b * (b - 1), n * (n - 1))
                checked += 1
    return checked


def rank_sequence(host):
    ranks = []
    for size in range(len(host) + 1):
        patterns = set()
        for values in combinations(host, size):
            ordered = {value: i for i, value in enumerate(sorted(values))}
            patterns.add(tuple(ordered[value] for value in values))
        ranks.append(len(patterns))
    return ranks


if __name__ == "__main__":
    assert rank_sequence((1, 2, 4, 3, 5, 7, 6, 8)) == [1, 1, 2, 3, 5, 8, 9, 5, 1]
    count = check_slice_curvature(25)
    print(f"Verified the sharp test over all bounded statistics in {count} finite slices and the size-eight rank vector.")
