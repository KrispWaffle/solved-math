"""Check the finite occurrence certificates and leading diagonal slopes in the proof."""

from functools import lru_cache
from itertools import combinations, permutations


def standardize(word):
    ranks = {value: idx for idx, value in enumerate(sorted(word), start=1)}
    return tuple(ranks[value] for value in word)


def inverse(word):
    return tuple(word.index(value) + 1 for value in range(1, len(word) + 1))


def reverse_complement(word):
    return tuple(len(word) + 1 - value for value in reversed(word))


def direct(*blocks):
    result = []
    for block in blocks:
        offset = len(result)
        result.extend(offset + value for value in block)
    return tuple(result)


def skew(left, right):
    return tuple(len(right) + value for value in left) + right


def increasing(length):
    return tuple(range(1, length + 1))


@lru_cache(maxsize=None)
def patterns(word, length):
    return frozenset(standardize(entries) for entries in combinations(word, length))


def decomposable(word):
    return any(max(word[:cut]) == cut for cut in range(1, len(word)))


def inversions(word):
    return sum(left > right for left, right in combinations(word, 2))


def templates(gamma, delta, boundary, overlap):
    """Return D if overlap is None, and J_t otherwise, clipping both long blocks at four."""
    left = direct(gamma, increasing(4))
    right = direct(increasing(4), delta)
    a, b = len(left), len(right)
    if overlap is None:
        tail = skew(right, (1,)) if boundary == "first-last" else skew((1,), right)
        return direct(skew((1,), left), tail)
    if boundary == "first-last":
        start, end = a + overlap + 2, a + 1
        middle = tuple(range(end + 1, start))
        return (start,) + left + middle + tuple(start + i for i in right) + (end,)
    start, maximum = a + overlap + 2, a + overlap + b + 3
    middle = tuple(range(a + 1, start))
    return (start,) + left + (maximum,) + middle + tuple(start + i for i in right)


def identity(word):
    return word


ORIENTATIONS = (("first-last", identity), ("first-last", inverse),
                ("first-maximum", identity), ("first-maximum", reverse_complement))
SECONDARY = ("1243", "1342", "1432", "2341", "3421", "4321")
TERTIARY = ("2143", "2413", "2431", "3412", "4231")
REPRESENTATIVES = tuple(tuple(map(int, p)) for p in SECONDARY + TERTIARY)


def small_words(length, forbidden):
    return (word for word in permutations(increasing(length))
            if forbidden not in patterns(word, 3))


def occurrence_certificates():
    differences = set()
    witnesses = 0
    for i in range(5):
        for j in range(5 - i):
            for gamma in small_words(i, (1, 3, 2)):
                for delta in small_words(j, (2, 1, 3)):
                    witnesses += 1
                    for boundary, symmetry in ORIENTATIONS:
                        base = patterns(templates(gamma, delta, boundary, None), 4)
                        variants = [patterns(templates(gamma, delta, boundary, t), 4)
                                    for t in range(5)]
                        assert (1, 3, 2, 4) not in base
                        assert all((1, 3, 2, 4) not in variant for variant in variants)
                        for pattern in REPRESENTATIVES:
                            target = symmetry(pattern)
                            if any((target in base) != (target in variant)
                                   for variant in variants):
                                differences.add(pattern)
    assert differences == set(REPRESENTATIVES[len(SECONDARY):])
    return witnesses


def decorations(bound, forbidden):
    yield (), 0
    for length in range(2, bound + 2):
        for word in small_words(length, forbidden):
            weight = inversions(word)
            if weight <= bound and not decomposable(word):
                yield word, weight


def first_slopes(bound):
    slopes = {p: [0] * (bound + 1) for p in REPRESENTATIVES}
    for gamma, left_weight in decorations(bound, (1, 3, 2)):
        for delta, right_weight in decorations(bound - left_weight, (2, 1, 3)):
            degree = left_weight + right_weight
            for boundary, symmetry in ORIENTATIONS:
                base = patterns(templates(gamma, delta, boundary, None), 4)
                variants = [patterns(templates(gamma, delta, boundary, t), 4)
                            for t in range(bound - degree + 1)]
                for pattern, coefficients in slopes.items():
                    target = symmetry(pattern)
                    coefficients[degree] += int(target not in base)
                    for t, variant in enumerate(variants):
                        if target not in variant:
                            coefficients[degree + t] -= 1
                            if degree + t < bound:
                                coefficients[degree + t + 1] += 1
    return slopes


if __name__ == "__main__":
    count = occurrence_certificates()
    slopes = first_slopes(2)
    print(f"Checked {count} pairs of witness patterns in four boundary orientations.")
    expected = {"2143": [-2, 0, 0], "2413": [3, 6, 15], "2431": [0, 1, 2],
                "3412": [0, 2, 4], "4231": [0, 0, 2]}
    for pattern, coefficients in slopes.items():
        label = "".join(map(str, pattern))
        print(label, coefficients)
        assert coefficients == expected.get(label, [0, 0, 0]), label
