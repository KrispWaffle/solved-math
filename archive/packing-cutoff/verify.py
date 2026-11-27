"""Count prescribed permutation packings directly from their window inequalities."""

from functools import cache
from math import comb


def patterns(k):
    """Return the two permutations of [4k], listed in position order."""
    first = []
    second = []
    for i in range(1, k + 1):
        first.extend((i, k + i, 2 * k + i, 4 * k + 1 - i))
        second.extend((i, k + i, 3 * k + 1 - i, 4 * k + 1 - i))
    return first, second


def packing_count(pattern, overlap, occurrences):
    """Count rank assignments by choosing the position of each successive rank."""
    length = len(pattern)
    assert sorted(pattern) == list(range(1, length + 1))
    step = length - overlap
    size = length + (occurrences - 1) * step
    prerequisites = [0] * size
    by_rank = sorted(range(length), key=pattern.__getitem__)
    for window in range(occurrences):
        start = window * step
        for low, high in zip(by_rank, by_rank[1:]):
            prerequisites[start + high] |= 1 << (start + low)

    full = (1 << size) - 1

    @cache
    def extensions(used):
        if used == full:
            return 1
        return sum(
            extensions(used | (1 << pos))
            for pos, required in enumerate(prerequisites)
            if not (used & (1 << pos)) and (required & used) == required
        )

    count = extensions(0)
    extensions.cache_clear()
    return count


def catalan(n):
    return comb(2 * n, n) // (n + 1)


if __name__ == "__main__":
    for k in range(2, 10):
        first, second = patterns(k)
        for j in range(1, k + 2):
            counts = tuple(packing_count(p, 4 * k - 4, j) for p in (first, second))
            baseline = catalan(j) ** 2
            excess = catalan(k) ** 2 if j == k + 1 else 0
            assert counts == (baseline + excess, baseline), (k, j, counts)
        print(f"k={k}, first difference at j={j}: {counts[0]} vs {counts[1]}")
