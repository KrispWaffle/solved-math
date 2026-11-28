"""Finite checks accompanying the prescribed-growth construction."""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, permutations, product
from math import factorial


def rank_order(entries):
    ranks = {entry: i for i, entry in enumerate(sorted(entries))}
    return tuple(ranks[entry] for entry in entries)


def indecomposable(perm):
    maximum = -1
    for i, x in enumerate(perm[:-1]):
        maximum = max(maximum, x)
        if maximum == i:
            return False
    return bool(perm)


def simple(perm):
    return all(max(window) - min(window) + 1 != len(window)
               for size in range(2, len(perm))
               for start in range(len(perm) - size + 1)
               for window in [perm[start:start + size]])


def inflate(base, cells):
    sizes = tuple(map(len, cells))
    return tuple(value + sum(sizes[j] for j in range(len(base)) if base[j] < base[i])
                 for i, cell in enumerate(cells) for value in cell)


def endpoint_tag(k, left, right):
    oscillation = [i + 4 if i % 2 == 0 else i for i in range(2*k + 5)]
    if k % 2 == 0:
        base = rank_order(oscillation[:k])
        right_index = base.index(k-1)
    else:
        least = set(sorted(oscillation)[:k])
        base = rank_order([entry for entry in oscillation if entry in least])
        right_index = k-1
    assert simple(base)
    cells = [(0,)] * k
    cells[base.index(0)], cells[right_index] = left, right
    return inflate(base, cells)


def deletions(perm):
    return {rank_order(perm[:i] + perm[i+1:]) for i in range(len(perm))}


def subpatterns(perm, size):
    return {rank_order(entries) for entries in combinations(perm, size)}


def tag_check(s, largest_base):
    decorations = tuple(permutations(range(s)))
    tags = {}
    for k in range(4, largest_base+1):
        level = {endpoint_tag(k, a, b) for a, b in product(decorations, repeat=2)}
        assert len(level) == factorial(s)**2
        assert all(indecomposable(tag) for tag in level)
        tags[k+2*(s-1)] = level

    # At entry to a size, descendants came only from strictly longer tags.
    descendants = set()
    checked = 0
    bound = 2*sum(factorial(i) for i in range(1, s+1))**2
    for size in range(max(tags), 2*s+1, -1):
        assert descendants.isdisjoint(tags[size])
        level = descendants | tags[size]
        assert sum(map(indecomposable, level)) <= bound
        checked += len(level)
        descendants = {child for perm in level for child in deletions(perm)}
    return sum(map(len, tags.values())), checked


def check_small_coefficients():
    counts = [0]
    for n in range(1, 7):
        count = factorial(n) - sum(counts[i]*factorial(n-i) for i in range(1, n))
        assert count == sum(map(indecomposable, permutations(range(n))))
        counts.append(count)
    assert counts[1:] == [1, 1, 3, 13, 71, 461]
    z = Fraction(4, 13)
    assert (sum(counts[i]*z**i for i in range(1, 6)) + 18*z**6/(1-z)
            == Fraction(306004, 371293) < 1)
    z3 = Fraction(1, 5)
    assert (sum(factorial(i)*z3**i for i in range(1, 8)) + 162*z3**8/(1-z3)
            == Fraction(80611, 156250) < 1)
    low = [1, 1, 3, 13, 71]
    assert (sum(v*z**i for i, v in enumerate(low, 1)) + 8*z**6/(1-z)
            == Fraction(2713076, 3341637) < 1)
    assert (sum(v*z**i for i, v in enumerate(counts[1:], 1)) + 11*z**7/(1-z)
            == Fraction(52018532, 43441281) > 1)

    # The two size-five replacements and their indecomposable proper patterns.
    first_tag = endpoint_tag(4, (0, 1), (0, 1))
    for star, only_child in [((1, 2, 3, 4, 0), (1, 2, 3, 0)),
                             ((4, 0, 1, 2, 3), (3, 0, 1, 2))]:
        assert {p for p in deletions(star) if indecomposable(p)} == {only_child}
        for k in range(1, 5):
            assert {p for p in subpatterns(star, k) if indecomposable(p)} <= subpatterns(first_tag, k)
        degrees = [sum((i-j)*(v-w) < 0 for j, w in enumerate(star)) for i, v in enumerate(star)]
        assert sorted(degrees) == [1, 1, 1, 1, 4]


def check_shifts():
    cell_count = fibre_count = 0
    for k in range(2, 6):
        for base in permutations(range(k)):
            if not indecomposable(base):
                continue
            for i in range(k):
                coeff = tuple(int(value < base[i]) - int(j < i) for j, value in enumerate(base))
                assert coeff[i] == 0 and any(coeff)
                cell_count += 1
                if k < 4 or not simple(base):
                    continue
                j = next(j for j in range(k) if coeff[j])
                fibres = defaultdict(set)
                for sizes in product(range(1, 5), repeat=k):
                    fixed = tuple(sizes[q] for q in range(k) if q not in (i, j))
                    key = (fixed, sum(sizes))
                    shift = sum(c*m for c, m in zip(coeff, sizes))
                    cells = [tuple(range(size)) for size in sizes]
                    member = inflate(base, cells)
                    first = sum(sizes[:i])
                    assert member[first]-first == shift
                    assert shift not in fibres[key]
                    fibres[key].add(shift)
                for shifts in fibres.values():
                    for radius in (0, 1, 2):
                        assert sum(abs(v) <= radius for v in shifts) <= 2*radius+1
                    fibre_count += 1
    return cell_count, fibre_count


def check_growth():
    check_small_coefficients()
    first = tag_check(2, 8)
    second = tag_check(3, 7)
    cells, fibres = check_shifts()
    return first[0]+second[0], first[1]+second[1], cells, fibres


if __name__ == "__main__":
    print(check_growth())
