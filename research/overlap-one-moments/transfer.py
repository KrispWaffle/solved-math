"""Mixed-binomial production matrix for original overlap-one packing counts."""

from functools import cache
from math import comb


def endpoint_moves(a, b, c, x, y):
    below = comb(x + 2 * a + c, a)
    for v in range(y + b + 1):
        ways = below * comb(v + c - 1, c - 1) * comb(y + 2 * b - v, b)
        yield (x + a + c + v, y + b - v), ways


def count(a, b, c, r):
    states = {(0, 0): 1}
    for _ in range(r):
        following = {}
        for (x, y), multiplicity in states.items():
            for state, weight in endpoint_moves(a, b, c, x, y):
                following[state] = following.get(state, 0) + multiplicity * weight
        states = following
    return sum(states.values())


@cache
def image(a, b, c, p, q, x, y):
    return sum(ways * comb(u, p) * comb(v, q)
               for (u, v), ways in endpoint_moves(a, b, c, x, y))


@cache
def entry(a, b, c, p, q, i, k):
    return sum((-1) ** (i + k - x - y) * comb(i, x) * comb(k, y) * image(a, b, c, p, q, x, y)
               for x in range(i + 1) for y in range(k + 1))


def return_count(a, b, c, r):
    d = a + b + c
    weights = {(0, 0): 1}
    for step in range(1, r + 1):
        following = {}
        for (p, q), multiplicity in weights.items():
            max_degree = min(p + q + d, (r - step) * d)
            for n in range(max_degree + 1):
                for i in range(n + 1):
                    state = (i, n - i)
                    m = entry(a, b, c, p, q, *state)
                    assert m >= 0
                    if m:
                        following[state] = following.get(state, 0) + multiplicity * m
        weights = following
    return weights.get((0, 0), 0)


if __name__ == "__main__":
    import runpy
    from itertools import permutations
    from pathlib import Path
    oracle = Path(__file__).resolve().parents[2] / "archive/packing-cutoff/verify.py"
    graph_count = runpy.run_path(str(oracle))["packing_count"]
    tested = 0
    for k in range(2, 6):
        for p in permutations(range(1, k + 1)):
            lo, hi = sorted((p[0], p[-1]))
            a, b, c = lo - 1, k - hi, hi - lo
            for r in range(4):
                assert count(a, b, c, r) == graph_count(p, 1, r + 1)
                tested += 1
    for a, b, c in ((0, 0, 1), (0, 2, 1), (1, 1, 3), (1, 2, 3)):
        for r in range(5):
            assert return_count(a, b, c, r) == count(a, b, c, r)
    u, v = ((0, 0), (1, 1)), ((0, 2), (2, 0))
    def block(rows, cols):
        return [[entry(1, 1, 3, *row, *col) for col in cols] for row in rows]
    assert block(u, v) == [[50, 0], [550, 4]]
    assert block(v, u) == [[0, 3], [210, 456]]
    print(f"{tested} direct counts agree. Return counts and opposite-sign transfer minors verified.")
