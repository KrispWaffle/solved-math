"""Check the constructions on actual interval intersections and connected branch sets."""

from functools import cache
from itertools import combinations
from random import Random

from check_gluing import check_gluing


def endpoint_pairings(points):
    """Match all endpoint orders, indexing intervals by their first endpoint."""
    if not points:
        yield ()
        return
    first, *others = points
    for last in others:
        remaining = [point for point in others if point != last]
        for rest in endpoint_pairings(remaining):
            yield ((first, last),) + rest


def check_dense_host(starts, width, order):
    @cache
    def branch(color, left, right):
        starts_in_branch = tuple(start for index, start in enumerate(starts)
                                 if index % order == color and start <= 3 * right * width
                                 and start + width >= 3 * left * width)
        assert starts_in_branch
        assert all(v <= u + width for u, v in zip(starts_in_branch, starts_in_branch[1:]))
        return starts_in_branch

    @cache
    def branches_adjacent(color, left, right, other_color, other_left, other_right):
        first = branch(color, left, right)
        second = branch(other_color, other_left, other_right)
        i = j = 0
        while i < len(first) and j < len(second):
            if abs(first[i] - second[j]) <= width:
                return True
            if first[i] < second[j]:
                i += 1
            else:
                j += 1
        return False

    targets = pairs = 0
    for intervals in endpoint_pairings(range(1, 2 * order + 1)):
        for color, (left, right) in enumerate(intervals):
            branch(color, left, right)
        for i, j in combinations(range(order), 2):
            left, right = intervals[i]
            other_left, other_right = intervals[j]
            actual = branches_adjacent(i, left, right, j, other_left, other_right)
            assert actual == (max(left, other_left) <= min(right, other_right))
            pairs += 1
        targets += 1
    return targets, pairs


def check_density():
    rng = Random(60267)
    targets = comparisons = 0
    width = 24
    for order in range(1, 7):
        end = 6 * order * width
        for _ in range(3):
            step = max(1, width // (order + 2))
            starts = sorted([*range(-width, end + 1, step),
                             *(rng.randrange(-width, end + 1) for _ in range(30))])
            # Integer endpoints make endpoints and midpoints sufficient to test coverage.
            for twice_x in range(2 * end + 1):
                assert sum(2 * t <= twice_x <= 2 * (t + width) for t in starts) >= order
            count, pairs = check_dense_host(starts, width, order)
            targets += count
            comparisons += pairs
    print(f"Dense intervals: {targets} target/host pairs, {comparisons} adjacencies and nonedges")


def check_closed_contacts():
    # Coordinates use tenths of a unit. Include ties at distance exactly one.
    width = 10
    for x, y in combinations(range(-31, 32), 2):
        first, second = sorted((x, y), key=lambda t: (t % width, -(t // width)))
        decoded = first // width in (second // width, second // width + 1)
        assert decoded == (abs(x - y) <= width)

    bull = (-9, 0, 4, 8, 17)
    branches = ((1, 3), (0,), (2,), (4,))
    for i, j in combinations(range(4), 2):
        adjacent = any(abs(bull[x] - bull[y]) <= width for x in branches[i] for y in branches[j])
        assert adjacent == (i == 0)
    assert abs(bull[1] - bull[3]) <= width


if __name__ == "__main__":
    check_closed_contacts()
    check_density()
    check_gluing()
