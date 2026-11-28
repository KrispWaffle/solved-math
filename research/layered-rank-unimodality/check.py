"""Exact coefficient checks for layered principal ideals."""
from functools import cache
from itertools import accumulate, product


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


if __name__ == "__main__":
    check()
