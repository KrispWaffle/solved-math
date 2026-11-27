"""Compare source-defined ranks with exact moments of the proposed spine density."""

from fractions import Fraction
from functools import cache
from math import comb, factorial, prod


def order_counts(m, a, b, n):
    """Glue chains directly at the two ranks in Definition 1.3."""
    windows = []
    size = 0
    for i in range(n):
        window = []
        for j in range(1, m + 1):
            if i and j == a:
                window.append(windows[-1][b - 1])
            else:
                window.append(size)
                size += 1
        windows.append(window)
    parents = [0] * size
    for window in windows:
        for lo, hi in zip(window, window[1:]):
            parents[hi] |= 1 << lo
    marks = [windows[0][a - 1]] + [w[b - 1] for w in windows]
    counts = {x: [0] * (size + 1) for x in marks}
    full = (1 << size) - 1

    def choices(mask):
        return [v for v, pred in enumerate(parents)
                if not mask & (1 << v) and not pred & ~mask]

    @cache
    def finish(mask):
        if mask == full:
            return 1
        return sum(finish(mask | (1 << v)) for v in choices(mask))

    partial = {0: 1}
    for rank in range(1, size + 1):
        following = {}
        for mask, multiplicity in partial.items():
            for v in choices(mask):
                nxt = mask | (1 << v)
                following[nxt] = following.get(nxt, 0) + multiplicity
                if v in counts:
                    counts[v][rank] += multiplicity * finish(nxt)
        partial = following
    assert partial[full] == finish(0)
    return finish(0), [counts[x] for x in marks]


def spine_integral(p, q, c, n, index=0, power=0):
    """Integrate z_index^power W(z) over the ordered simplex with rational arithmetic."""
    poly = [Fraction(1)]
    for s in range(c * n + 1):
        left = p if s % c == 0 and s < c * n else 0
        right = q if s % c == 0 and s > 0 else 0
        shift = left + (power if s == index else 0)
        nxt = [Fraction(0)] * (len(poly) + shift + right + 1)
        for k, value in enumerate(poly):
            for h in range(right + 1):
                j = k + shift + h + 1
                nxt[j] += value * (-1)**h * comb(right, h) / j
        poly = nxt
    return sum(poly)


def rising(a, j):
    return prod(range(a, a + j))


def check(m, a, b, n):
    p, q, c = a - 1, m - b, b - a
    d = (m - 1) * n + 1
    total, marginals = order_counts(m, a, b, n)
    mass = spine_integral(p, q, c, n)
    assert mass * factorial(d) / (factorial(p) * factorial(q))**n == total
    for i, counts in enumerate(marginals):
        assert sum(counts) == total
        # Powers 0 through d-1 identify all d possible rank weights, since
        # rising(k,j) has degree j and the distinct evaluation points are 1,...,d.
        for power in range(1, d):
            expected = sum(count * rising(rank, power) for rank, count in enumerate(counts))
            moment = Fraction(expected, total * rising(d + 1, power))
            assert spine_integral(p, q, c, n, c * i, power) / mass == moment
    return len(marginals)


if __name__ == '__main__':
    stacks = ranks = 0
    for m in range(2, 7):
        for a in range(1, m):
            for b in range(a + 1, m + 1):
                for n in range(1, 4):
                    ranks += check(m, a, b, n)
                    stacks += 1
    print(f'Exact extension counts and all {ranks} marked rank distributions match '
          f'the spine integrals in {stacks} stacks.')
