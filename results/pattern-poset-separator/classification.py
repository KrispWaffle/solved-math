"""Separator classification for arbitrary compatible permutation patterns.

Public functions take a permutation of 1 through K. Rank slots use zero-based
window and rank indices. Only the boundary ranks enter the comparison tables.
"""

from bisect import bisect_right
from functools import cache
from itertools import permutations


def transfer_powers(k, source, destination):
    step = tuple(
        min((dst for src, dst in zip(source, destination) if src >= rank), default=k)
        for rank in range(k + 1)
    )
    powers = [tuple(range(k + 1))]
    for _ in range(k):
        following = tuple(step[old] for old in powers[-1])
        if following == powers[-1]:
            break
        powers.append(following)
    return tuple(powers)


@cache
def boundary_tables(k, prefix, suffix):
    if sorted(range(len(prefix)), key=prefix.__getitem__) != sorted(
        range(len(suffix)), key=suffix.__getitem__
    ):
        raise ValueError("the prefix and suffix have different relative order")
    return transfer_powers(k, suffix, prefix), transfer_powers(k, prefix, suffix)


def order_masks(pattern, overlap, windows):
    """Weak upper and lower sets, one bit for each window/rank slot."""
    k = len(pattern)
    if sorted(pattern) != list(range(1, k + 1)) or not 0 < overlap < k or windows < 0:
        raise ValueError("expected a permutation, a proper positive overlap, and a nonnegative count")
    prefix = tuple(x - 1 for x in pattern[:overlap])
    suffix = tuple(x - 1 for x in pattern[-overlap:])
    forward, backward = boundary_tables(k, prefix, suffix)
    block = (1 << k) - 1
    upper, lower = [], []
    for row in range(windows):
        up = [0] * k
        down = [0] * k
        for other in range(windows):
            distance = abs(other - row)
            out, into = (forward, backward) if row <= other else (backward, forward)
            out = out[min(distance, len(out) - 1)]
            into = into[min(distance, len(into) - 1)]
            start = other * k
            for rank in range(k):
                up[rank] |= (block ^ ((1 << out[rank]) - 1)) << start
                down[rank] |= ((1 << bisect_right(into, rank, 0, k)) - 1) << start
        upper.extend(up)
        lower.extend(down)
    return upper, lower


def separator_slots(pattern, overlap, windows):
    """All representatives of separators in a stack of the specified actual length."""
    upper, lower = order_masks(pattern, overlap, windows)
    comparable = [u | l for u, l in zip(upper, lower)]
    full = (1 << len(comparable)) - 1

    def nonchain(side):
        remaining = side
        while remaining:
            bit = remaining & -remaining
            if side & ~comparable[bit.bit_length() - 1]:
                return True
            remaining ^= bit
        return False

    return [divmod(i, len(pattern)) for i, seen in enumerate(comparable)
            if seen == full and nonchain(lower[i]) and nonchain(upper[i])]


def has_separator(pattern, overlap, windows):
    return bool(separator_slots(pattern, overlap, min(windows, 4 * len(pattern) + 1)))


def always_has_separator(pattern, overlap):
    if not 0 < overlap < len(pattern):
        raise ValueError("expected a proper positive overlap")
    return all(has_separator(pattern, overlap, j) for j in range(overlap + 1, 4 * len(pattern) + 2))


def crosscheck(order, is_separator):
    """Use the original physical-position graph as the independent oracle."""
    tested = 0
    for k in range(2, 6):
        for pattern in permutations(range(1, k + 1)):
            inverse = sorted(range(k), key=pattern.__getitem__)
            for m in range(1, k):
                if sorted(range(m), key=pattern.__getitem__) != sorted(
                    range(m), key=pattern[-m:].__getitem__
                ):
                    continue
                d = k - m
                for j in range(1, 6):
                    raw = order(pattern, m, j)
                    actual = [d*t + i for t in range(j) for i in inverse]
                    up, down = order_masks(pattern, m, j)
                    for a, x in enumerate(actual):
                        expected = sum(1 << b for b, y in enumerate(actual)
                                       if x == y or raw[x] & (1 << y))
                        assert up[a] == expected, (pattern, m, j, a, "upper")
                        expected = sum(1 << b for b, y in enumerate(actual)
                                       if x == y or raw[y] & (1 << x))
                        assert down[a] == expected, (pattern, m, j, a, "lower")
                    expected = {z for z in range(len(raw)) if is_separator(raw, z)}
                    classified = {d*t + inverse[r] for t, r in separator_slots(pattern, m, j)}
                    assert classified == expected, (pattern, m, j)
                    tested += 1
    for word, m, j, count in (("135268479", 3, 4, 3), ("479258136", 6, 7, 5)):
        pattern = tuple(map(int, word))
        inverse = sorted(range(len(pattern)), key=pattern.__getitem__)
        labels = {(len(pattern)-m)*t + inverse[r] for t, r in separator_slots(pattern, m, j)}
        assert len(labels) == count
        for windows in (4*len(pattern)+1, 4*len(pattern)+2, 4*len(pattern)+5):
            raw = order(pattern, m, windows)
            assert has_separator(pattern, m, windows) == any(
                is_separator(raw, z) for z in range(len(raw))
            )
    for j, labels in ((2, {3}), (3, set())):
        raw = order((2,1,4,3), 1, j)
        assert {z for z in range(len(raw)) if is_separator(raw, z)} == labels
        assert has_separator((2,1,4,3), 1, j) == bool(labels)
    assert always_has_separator((1,3,2,5,7,8,4,6), 2)
    assert not always_has_separator((1,2,3,4), 3)
    assert has_separator((1,3,2,5,7,8,4,6), 2, 10**20)
    print(f"Rank comparisons and separator labels agree with the physical poset in {tested} stacks.")


if __name__ == "__main__":
    from verify import is_separator, order
    crosscheck(order, is_separator)
