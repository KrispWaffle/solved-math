"""Exact coefficient checks for layered principal ideals."""
from fractions import Fraction
from functools import cache
from itertools import accumulate, product
from math import prod


def compositions(n):
    if n == 0:
        yield ()
        return
    for i in range(1, n + 1):
        for tail in compositions(n - i):
            yield (i,) + tail


@cache
def words(host):
    if not host:
        return {()}
    head, tail = host[0], words(host[1:])
    return tail | {(a,) + suffix for a in range(1, head + 1) for suffix in tail}


def convolution(left, right):
    out = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i+j] += a*b
    return out


def coefficient(values, i):
    return values[i] if 0 <= i < len(values) else 0


@cache
def peak_polynomial(host):
    if not host:
        return (1,)
    m = max(host)
    at = host.index(m)
    a, b = peak_polynomial(host[:at]), peak_polynomial(host[at+1:])
    ab = convolution(a, b)
    prefix = [0, *accumulate(ab)]
    def partial(r):
        return prefix[min(max(r, 0), len(ab))]
    return tuple(coefficient(a, r) + coefficient(b, r) - coefficient(ab, r)
                 + partial(r) - partial(r-m) for r in range(sum(host)+1))


def exact_greedy_boxes(host):
    seen = set()
    for mask in product([False, True], repeat=len(host)):
        ranges = []
        gap = 0
        for w, chosen in zip(host, mask):
            if chosen:
                ranges.append(range(gap+1, w+1))
                gap = 0
            else:
                gap = max(w, gap)
        for member in product(*ranges):
            assert member not in seen
            seen.add(member)
    return seen


def centered_strings(widths):
    by_width = {0: 1}
    for width in widths:
        out = {}
        for old, count in by_width.items():
            for new in range(abs(old-width), old+width+1, 2):
                out[new] = out.get(new, 0) + count
        by_width = out
    return by_width


def check_strings():
    cases = 0
    for widths in product(range(5), repeat=5):
        actual = [1]
        for width in widths:
            actual = convolution(actual, [1]*(width+1))
        total = sum(widths)
        mult = centered_strings(widths)
        for r in range(total+1):
            assert actual[r] == sum(n for h, n in mult.items() if abs(2*r-total) <= h)
        cases += 1
    return cases


def check_host(host, direct):
    counts = peak_polynomial(host)
    weight, k = sum(host), len(host)
    assert counts == peak_polynomial(host[::-1]) and min(counts) > 0
    if direct:
        originals = words(host)
        assert exact_greedy_boxes(host) == originals
        histogram = [0]*(weight+1)
        for pattern in originals:
            histogram[sum(pattern)] += 1
        assert tuple(histogram) == counts
    if not host:
        return 0
    c = (weight+k-1)//2
    assert all(counts[r] >= counts[r+1] for r in range(c, weight))
    if k < 2:
        return 0
    major = sum(sorted(host)[-2:])
    degrees = range(weight-major+3, min(major+2, weight+3))
    for j in degrees:
        assert (coefficient(counts, j) - 2*coefficient(counts, j-1)
                + coefficient(counts, j-2)) <= 0
    return len(degrees)


def period_polynomials(v):
    at = v.index(max(v))
    gap = v[at+1:] + v[:at]
    g, h = peak_polynomial(gap), peak_polynomial(v)
    extended = peak_polynomial(gap + (max(v),))
    q = tuple(value - coefficient(g, n) for n, value in enumerate(extended))
    first = next(n for n, value in enumerate(q) if value)
    assert all(value > 0 for value in q[first:])
    return q, g, h


def next_period(old, q, g):
    values = convolution(q, old)
    for i, x in enumerate(g):
        values[i] += x
    return values


def check_periods():
    transitions = 0
    for k in range(1, 5):
        for v in product(range(1, 5), repeat=k):
            q, g, h = period_polynomials(v)
            previous = h
            for m in range(2, 5):
                previous = next_period(previous, q, g)
                assert tuple(previous) == peak_polynomial(v*m)
                transitions += 1
    return transitions


def check_period_modes():
    cases = 0
    for v in [(2,), (1, 2, 1, 3), (3, 1, 2, 1), (3, 2, 4, 1, 3), (1, 3, 2, 3)]:
        q, g, h = period_polynomials(v)
        def derivative(p):
            return sum(i*a for i, a in enumerate(p))
        mass = sum(q)
        mean = Fraction(derivative(q), mass)
        variance = sum((i-mean)**2*a for i, a in enumerate(q))/mass
        third = sum((i-mean)**3*a for i, a in enumerate(q))/mass
        b0 = sum(h) + Fraction(sum(g), mass-1)
        b1 = derivative(h) + Fraction(derivative(g), mass-1) - Fraction(sum(g)*derivative(q), (mass-1)**2)
        ranks = h
        for m in range(2, 101):
            ranks = next_period(ranks, q, g)
            if m in (60, 80, 100):
                predicted = (m-1)*mean + b1/b0 - third/(2*variance)
                closest = min(abs(i-predicted) for i in (predicted.__floor__(), predicted.__ceil__()))
                mode_set = [i for i, value in enumerate(ranks) if value == max(ranks)]
                assert all(abs(i-predicted) == closest for i in mode_set), (v, m, predicted, mode_set)
                cases += 1
    return cases



def maximum_gaps(host, maximum):
    gaps = [[]]
    for part in host:
        if part == maximum:
            gaps.append([])
        else:
            gaps[-1].append(part)
    return [tuple(gap) for gap in gaps]


def check_block_factorization(host):
    maximum = max(host)
    gaps = maximum_gaps(host, maximum)
    a = peak_polynomial(host)
    exits = []
    for gap in gaps:
        base = peak_polynomial(gap)
        extended = peak_polynomial(gap + (maximum,))
        exits.append(tuple(v - coefficient(base, i) for i, v in enumerate(extended)))
    # Move an end gap into the interior and reconstruct the literal host.
    reordered = gaps[1::2] + gaps[::2]
    permuted = tuple(n for gap in reordered[:-1] for n in (*gap, maximum)) + reordered[-1]
    assert peak_polynomial(permuted) == a
    p = [1]
    for q in exits:
        p = convolution(p, q)
    assert tuple(p) == tuple(int(r == 0) - coefficient(a, r) +
                             sum(coefficient(a, r-s) for s in range(1, maximum+1))
                             for r in range(sum(host)+maximum+1))
    def moments(q):
        mass = sum(q)
        mean = Fraction(sum(i*v for i, v in enumerate(q)), mass)
        variance = Fraction(sum(i*i*v for i, v in enumerate(q)), mass) - mean**2
        return mean, variance
    mass = prod(sum(q) for q in exits)
    assert (maximum-1)*sum(a) == mass-1
    mean, variance = map(sum, zip(*(moments(q) for q in exits)))
    scale = Fraction(mass, mass-1)
    shift = Fraction(sum(range(1, maximum+1)), maximum-1)
    correction = Fraction(sum(i*i for i in range(1, maximum+1)), maximum-1)-shift**2
    assert moments(a) == (scale*mean-shift, scale*variance-scale*mean**2/(mass-1)-correction)


def check_varying_blocks():
    tested = 0
    for length in range(1, 7):
        for host in product((1, 2, 3), repeat=length):
            if max(host) >= 2:
                check_block_factorization(host)
                tested += 1
    # A deterministic nonperiodic sequence of distinctly ordered gap types.
    types = ((), (1,), (1, 2), (2, 1, 2), (2, 2, 1), (1, 1, 2, 1, 1))
    for m in (31, 62, 93):
        gaps = [types[(i.bit_count()+i.bit_length()) % len(types)] for i in range(m+1)]
        host = tuple(n for gap in gaps[:-1] for n in (*gap, 3)) + gaps[-1]
        check_block_factorization(host)
        ranks = peak_polynomial(host)
        peak = ranks.index(max(ranks))
        assert list(ranks[:peak+1]) == sorted(ranks[:peak+1])
        assert list(ranks[peak:]) == sorted(ranks[peak:], reverse=True)
        tested += 1
    return tested

def check():
    tested = inequalities = 0
    for n in range(11):
        for host in compositions(n):
            inequalities += check_host(host, True)
            tested += 1
    for host in product((1, 3, 4), repeat=7):
        inequalities += check_host(host, False)
        tested += 1
    # Long unequal scales with two largest parts on both sides of smaller arms.
    for capacities in [(2, 9, 1, 127, 3, 146, 5, 1), (201, 7, 2, 211, 1, 9),
                       (50, 1, 40, 1, 60, 2, 70, 1), (1, 2, 100, 100, 117, 3)]:
        inequalities += check_host(capacities, False)
        tested += 1
    # In this vanishing-coordinate family the thick-shape peak formula need not hold.
    for s in range(4, 17):
        host = (1, 1, 2*s, 2*s, 2*s)
        ranks = peak_polynomial(host)
        assert ranks[3*s+2] - ranks[3*s+1] == 5
        assert ranks[3*s+3] - ranks[3*s+2] == -1
        assert [i for i, value in enumerate(ranks) if value == max(ranks)] == [3*s+2]
    for a in [(9, 2, 8, 1, 7, 3, 5), (2, 5, 1, 6, 4, 3, 8, 5)]:
        host = tuple(8*i for i in a)
        ranks = peak_polynomial(host)
        assert ranks[(len(host)+sum(host)-1)//2] == max(ranks)
    print(f"Checked {tested} hosts, {inequalities} two-peak second differences, "
          f"and {check_strings()} tensor string decompositions.")
    print(f"Checked {check_periods()} periodic transitions and {check_period_modes()} exact peak-location examples.")
    print(f"Checked block products, gap permutations and both exact rank moments on {check_varying_blocks()} hosts.")


if __name__ == "__main__":
    check()
