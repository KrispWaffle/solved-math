"""Check separators directly from the integer positions in prescribed windows."""

from itertools import combinations, permutations


def order(pattern, overlap, windows):
    """Transitive closure of the adjacent-rank inequalities in all windows."""
    length = len(pattern)
    stride = length - overlap
    size = length + (windows - 1) * stride
    above = [0] * size
    positions = sorted(range(length), key=pattern.__getitem__)
    for window in range(windows):
        start = window * stride
        for left, right in zip(positions, positions[1:]):
            above[start + left] |= 1 << (start + right)
    for middle, successors in enumerate(above):
        middle_bit = 1 << middle
        for lower in range(size):
            if above[lower] & middle_bit:
                above[lower] |= successors
    if any(successors & (1 << x) for x, successors in enumerate(above)):
        raise ValueError("the prescribed windows contain a directed cycle")
    return above


def is_separator(above, z):
    lower = [x for x, successors in enumerate(above) if successors & (1 << z)]
    upper = [x for x in range(len(above)) if above[z] & (1 << x)]

    def has_incomparable_pair(side):
        return any(
            not (above[x] & (1 << y) or above[y] & (1 << x))
            for x, y in combinations(side, 2)
        )

    return (
        1 + len(lower) + len(upper) == len(above)
        and has_incomparable_pair(lower)
        and has_incomparable_pair(upper)
    )


def verify():
    checked = 0
    paper_cases = 0
    counts = {}
    for overlap in range(2, 5):
        # Enumerate all eligible boundary ranks up to the length bound.
        # Exercise every middle order through length eight and both extremes above it.
        for length in range(2 * overlap + 2, 12):
            for ranks in combinations(range(2, length + 1), 2 * overlap - 1):
                prefix = (1,) + ranks[: overlap - 1]
                suffix = ranks[overlap - 1 :]
                if not any(
                    prefix[i] + 1 < prefix[i + 1] and suffix[i] + 1 < suffix[i + 1]
                    for i in range(overlap - 1)
                ):
                    continue
                middle = tuple(sorted(set(range(1, length + 1)) - set(ranks) - {1}))
                arrangements = permutations(middle) if length <= 8 else (middle, middle[::-1])
                for interior in arrangements:
                    pattern = prefix + interior + suffix
                    for windows in (3, 4, 5):
                        assert is_separator(order(pattern, overlap, windows), length - 1), (
                            pattern, overlap, windows
                        )
                        checked += 1
                        counts[overlap] = counts.get(overlap, 0) + 1
                        if overlap == 2 and suffix[-1] - 1 < length - 2:
                            paper_cases += 1
    # Item 5 supplies these counts for patterns outside the sufficient condition.
    for word, overlap, windows, expected in (
        ("135268479", 3, 4, 3),
        ("479258136", 6, 7, 5),
    ):
        above = order(tuple(map(int, word)), overlap, windows)
        assert sum(is_separator(above, z) for z in range(len(above))) == expected
    # A chain fails the two nonchain conditions even if every vertex is comparable.
    assert not is_separator(order((1, 2, 3, 4), 2, 3), 3)
    # With only two windows and the maximum at the last position, the upper side is a chain.
    assert not is_separator(order((1, 3, 2, 5, 4, 6), 2, 2), 5)
    print(f"{checked} posets verified by transitive closure, including {paper_cases} paper cases")
    print(", ".join(f"overlap {m}: {n}" for m, n in sorted(counts.items())))


if __name__ == "__main__":
    verify()
