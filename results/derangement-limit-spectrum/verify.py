"""Check the finite permutation identities and Vatter interval bounds by exact arithmetic."""

from fractions import Fraction
from itertools import permutations

from verify_polynomial import check_polynomial
from verify_growth import check_growth


def direct(left, right):
    return left + tuple(len(left) + x for x in right)


def skew(left, right):
    return tuple(len(right) + x for x in left) + right


def no_fixed_points(permutation):
    return all(value != index for index, value in enumerate(permutation))


def direct_sizes(permutation):
    sizes = []
    start = 0
    largest = -1
    for i, x in enumerate(permutation):
        largest = max(largest, x)
        if largest == i:
            sizes.append(i + 1 - start)
            start = i + 1
    return sizes


def deletion(permutation, i):
    omitted = permutation[i]
    return tuple(x - (x > omitted) for j, x in enumerate(permutation) if j != i)


def identities():
    levels = [list(permutations(range(n))) for n in range(9)]
    pairs = 0
    for n in range(len(levels)):
        for m in range(n + 1):
            h = n - m
            for left in levels[m]:
                for right in levels[h]:
                    pairs += 1
                    pi = skew(left, right)
                    expected = all(h + x != i for i, x in enumerate(left)) and all(
                        x != m + j for j, x in enumerate(right)
                    )
                    assert no_fixed_points(pi) == expected
                    assert no_fixed_points(direct(left, right)) == (
                        no_fixed_points(left) and no_fixed_points(right)
                    )
                    if left and right:
                        assert direct_sizes(pi) == [n]
                        if max(direct_sizes(left)) <= h and max(direct_sizes(right)) <= m:
                            assert expected
    return pairs


def bounded_layers(bound, limit):
    levels = [{()}]
    for n in range(1, limit + 1):
        level = set()
        for j in range(1, min(n, bound) + 1):
            layer = tuple(reversed(range(j)))
            level.update(direct(layer, suffix) for suffix in levels[n-j])
        levels.append(level)
    return levels


def skew_classes(levels):
    result = []
    for n in range(len(levels)):
        outputs = set()
        unique = set()
        marked_good = 0
        for m in range(n + 1):
            for left in levels[m]:
                for right in levels[n-m]:
                    pi = skew(left, right)
                    outputs.add(pi)
                    if len(direct_sizes(left)) > 1 and len(direct_sizes(right)) > 1:
                        marked_good += 1
                        unique.add(pi)
        assert len(unique) == marked_good
        assert all(pi in levels[n] for pi in outputs if len(direct_sizes(pi)) > 1)
        result.append(outputs)
    return result


def check_classes():
    limit = 12
    slow = bounded_layers(2, limit)
    fast = bounded_layers(3, limit)
    carrier = skew_classes(slow)
    decoration = [
        (carrier[n] if n <= 5 else set()) | (fast[n] if n <= 4 else set())
        for n in range(6)
    ]
    decorated = []
    unique_count = 0
    for n in range(limit + 1):
        good = set()
        bad = set()
        free_pairs = 0
        for j in range(min(n, len(decoration)-1) + 1):
            for left in carrier[n-j]:
                for tail in decoration[j]:
                    pi = direct(left, tail)
                    free_pairs += no_fixed_points(left) and no_fixed_points(tail)
                    if len(direct_sizes(left)) == 1:
                        assert pi not in good
                        good.add(pi)
                    else:
                        bad.add(pi)
        outputs = good | bad
        assert sum(map(no_fixed_points, outputs)) <= free_pairs
        decorated.append(outputs)
        unique_count += len(good)
    for levels in (slow, fast, carrier, decoration, decorated):
        for n in range(1, len(levels)):
            for pi in levels[n]:
                assert all(deletion(pi, i) in levels[n-1] for i in range(n))
    # Recognize membership by all possible cuts on an independently enumerated host.
    for n in range(9):
        recovered = set()
        for pi in permutations(range(n)):
            for m in range(n + 1):
                shift = n - m
                if (tuple(x - shift for x in pi[:m]) in slow[m]
                        and pi[m:] in slow[shift]):
                    recovered.add(pi)
                    break
        assert recovered == carrier[n]
    return len(decorated[limit]), unique_count


def interval():
    def indecomposable_series(z, first_four, tail):
        return sum(n * z**j for j, n in enumerate(first_four, 1)) + tail * z**5 / (1-z)

    slower = indecomposable_series(Fraction(2, 5), (1, 1, 3, 5), 6)
    faster = indecomposable_series(Fraction(5, 13), (1, 1, 3, 13), 8)
    assert slower == Fraction(614, 625) < 1 < faster == Fraction(31335, 28561)


if __name__ == "__main__":
    interval()
    pairs = identities()
    members, unique = check_classes()
    print(f"Derangement spectrum: {pairs} permutation pairs, "
          f"{members} distinct decorated members at length 12, "
          f"{unique} uniquely recovered direct-sum pairs across lengths.")
    boxes, rational_slices = check_polynomial()
    print(f"Polynomial classes: {boxes} exact monotone inflations and {rational_slices} rational-witness slices.")
    tags, patterns, cells, fibres = check_growth()
    print(f"Prescribed growth: {tags} antichain tags, {patterns} distinct tag subpatterns across the checked levels, "
          f"{cells} active cells and {fibres} fixed-total displacement fibres.")
