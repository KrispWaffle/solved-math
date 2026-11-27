"""Compare prescribed pattern occurrences with empty-to-empty exclusion walks."""

from collections import defaultdict
from functools import cache
from fractions import Fraction
from itertools import combinations_with_replacement, permutations
from math import comb, factorial

from periodic import LayerGraph


def packing_extensions(height, width):
    # For the odd-then-even pattern each sorted rank locates a physical position.
    n = height * width
    predecessors = [0] * n
    for occurrence in range(width - 1):
        start = occurrence * height
        chain = [
            start + level + offset
            for level in range(height)
            for offset in (0, height)
        ]
        for a, b in zip(chain, chain[1:]):
            predecessors[b] |= 1 << a

    return count_ideals(predecessors)


def count_ideals(predecessors):
    n = len(predecessors)

    @cache
    def extensions(used):
        if used == (1 << n) - 1:
            return 1
        return sum(
            extensions(used | (1 << k))
            for k, required in enumerate(predecessors)
            if not used & (1 << k) and not required & ~used
        )

    return extensions(0)


def empty_returns(width, max_height):
    last = 1 << (width - 2)
    ways = {0: 1}
    result = [1]
    for step in range(1, width * max_height + 1):
        following = defaultdict(int)
        for state, count in ways.items():
            if not state & 1:
                following[state | 1] += count
            for k in range(width - 2):
                edge = 3 << k
                if state & edge == 1 << k:
                    following[state ^ edge] += count
            if state & last:
                following[state ^ last] += count
        ways = following
        if step % width == 0:
            result.append(ways[0])
    return result


def subdivided_physical(horizontal, vertical, windows):
    height = len(horizontal)
    left, right = [], []
    first = 1
    for i, h in enumerate(horizontal):
        left.append(first)
        right.append(first + h + 1)
        if i + 1 < height:
            first = right[-1] + vertical[i] + 1
    length = right[-1]
    middle = sorted(set(range(1, length + 1)) - set(left) - set(right))
    pattern = left + middle + right
    positions = sorted(range(length), key=pattern.__getitem__)
    stride = length - height
    predecessors = [0] * (height + windows * stride)
    for q in range(windows):
        for a, b in zip(positions, positions[1:]):
            predecessors[q * stride + b] |= 1 << (q * stride + a)
    return count_ideals(predecessors)


def check_periodic():
    comparisons = 0
    for horizontal, vertical in [
        ((0,), (0,)), ((1,), (0,)), ((0,), (1,)), ((1,), (2,)),
        ((0, 2), (1, 0)), ((2, 0), (1, 2)), ((0, 1, 0), (0, 2, 1)),
    ]:
        p = len(horizontal)
        for windows in range(1, 5):
            graph = LayerGraph(windows, horizontal, vertical)
            for height in range(2, 7):
                h = tuple(horizontal[i % p] for i in range(height))
                v = tuple(vertical[i % p] for i in range(height - 1))
                if height + windows * (height + sum(h) + sum(v)) > 56:
                    continue
                expected = subdivided_physical(h, v, windows)
                actual = graph.packing(height)
                assert actual == expected, (h, v, windows, actual, expected)
                comparisons += 1
    # Compare rigorous rational bounds at a nonzero subdivision profile.
    bounds = [LayerGraph(j, (0, 1), (1, 0)).growth_bounds(4) for j in range(1, 5)]
    assert bounds[1] == (30, 30)
    assert bounds[0][0] * bounds[2][0] > bounds[1][1] ** 2
    assert bounds[1][0] * bounds[3][0] > bounds[2][1] ** 2
    return comparisons


def integrated_count(horizontal, vertical, windows):
    """Integrate each vertical-chain simplex over the horizontal order chambers."""
    m = len(horizontal)
    strides = [h + 1 for h in horizontal]
    sizes = [windows * a + 1 for a in strides]
    ranks = [[] for _ in range(m)]

    def vertical_weight():
        intervals = []
        for i, v in enumerate(vertical):
            for q in range(windows):
                low = ranks[i][(q + 1) * strides[i]]
                high = ranks[i + 1][q * strides[i + 1]]
                if low >= high:
                    return 0
                if v:
                    intervals.append((low, high, v))
        occupancy = [0] * sum(sizes)

        def allocate(i):
            if i == len(intervals):
                return 1
            low, high, v = intervals[i]
            total = 0
            for slots in combinations_with_replacement(range(low, high), v):
                used = {slot: slots.count(slot) for slot in set(slots)}
                weight = 1
                for slot, count in used.items():
                    weight *= comb(occupancy[slot] + count, count)
                    occupancy[slot] += count
                total += weight * allocate(i + 1)
                for slot, count in used.items():
                    occupancy[slot] -= count
            return total

        return allocate(0)

    def interleave(rank):
        if rank == sum(sizes):
            return vertical_weight()
        total = 0
        for i, size in enumerate(sizes):
            k = len(ranks[i])
            if k == size:
                continue
            if i and k % strides[i] == 0 and k // strides[i] < windows:
                required = (k // strides[i] + 1) * strides[i - 1]
                if len(ranks[i - 1]) <= required:
                    continue
            ranks[i].append(rank)
            total += interleave(rank + 1)
            ranks[i].pop()
        return total

    return interleave(0)


def check_integral():
    examples = [
        ((0, 0), (0,), 5), ((1, 0), (2,), 3), ((1, 1), (1,), 3),
        ((0, 0, 0), (1, 1), 3), ((1, 0, 1), (0, 1), 2),
        ((0, 0, 0, 0), (0, 1, 0), 2),
    ]
    for h, v, windows in examples:
        horizontal_integral = integrated_count(h, v, windows)
        physical = subdivided_physical(h, v, windows)
        assert horizontal_integral == physical, (h, v, windows, horizontal_integral, physical)
    return len(examples)


def check_reflection():
    comparisons = 0
    for x, y in [
        ((2, 1), (8, 6)), ((4, 3), (12, 5)),
        ((3, 2, 1), (7, 5, 4)), ((6, 3, 1), (9, 7, 3)),
        ((5, 4, 3, 1), (9, 7, 5, 2)), ((5, 3, 2, 1), (8, 7, 6, 5)),
    ]:
        @cache
        def walks(state):
            if state == y:
                return 1
            result = 0
            for i, coordinate in enumerate(state):
                if coordinate == y[i] or (i and coordinate + 1 == state[i - 1]):
                    continue
                dest = list(state)
                dest[i] += 1
                result += walks(tuple(dest))
            return result

        m = len(x)
        det = Fraction(0)
        for perm in permutations(range(m)):
            gaps = [y[perm[i]] - x[i] for i in range(m)]
            if min(gaps) < 0:
                continue
            sign = (-1) ** sum(perm[i] > perm[j] for i in range(m) for j in range(i + 1, m))
            product = Fraction(sign * factorial(sum(gaps)))
            for gap in gaps:
                product /= factorial(gap)
            det += product
        assert det == walks(x), (x, y, det, walks(x))
        comparisons += 1
    return comparisons


def main():
    checks = 0
    for width in range(2, 12):
        max_height = min(10, 58 // width)
        returns = empty_returns(width, max_height)
        for height in range(2, max_height + 1):
            physical = packing_extensions(height, width)
            assert physical == returns[height], (height, width, physical, returns[height])
            checks += 1
    print(f"Matched {checks} exact packing counts to exclusion-walk returns.")
    print(f"Matched {check_periodic()} subdivided grid counts to the periodic transfer.")
    print(f"Matched {check_reflection()} chamber determinants to direct walks.")
    print(f"Matched {check_integral()} exact row integrals to physical-position counts.")


if __name__ == "__main__":
    main()
