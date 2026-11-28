"""Compare the slope-cell membership proof with literal finite induced subgraphs."""
from functools import cache
from itertools import combinations, permutations, product
from math import isqrt
from random import Random


@cache
def rotation_floor(i, radicand):
    """Floor of i*(sqrt(radicand)-1)/2, for positive and negative indices."""
    if i < 0:
        return -1 - rotation_floor(-i, radicand)
    return (isqrt(radicand * i * i) - i) // 2


def bit(i, radicand):
    return rotation_floor(i + 1, radicand) - rotation_floor(i, radicand)


@cache
def is_factor(word, radicand):
    prefix = [0]
    for digit in word:
        prefix.append(prefix[-1] + digit)
    # All nonzero multiples of the slope are irrational, so the strict
    # upper bound can be tested using their integer floors.
    return all(
        prefix[i] - prefix[j] <= 1 + rotation_floor(i - j, radicand)
        for i in range(len(prefix)) for j in range(len(prefix)) if i != j
    )


@cache
def edges(n):
    return tuple(combinations(range(n), 2))


def literal_fold(positions, radicand):
    digits = [bit(i, radicand) for i in positions]
    mask = 0
    for k, (u, v) in enumerate(edges(len(positions))):
        adjacent = abs(positions[u] - positions[v]) == 1
        if adjacent ^ bool(digits[u] and digits[v]):
            mask |= 1 << k
    return mask


def relabel(n, mask, order):
    edge_bits = {pair: mask >> k & 1 for k, pair in enumerate(edges(n))}
    return sum(edge_bits[tuple(sorted((order[u], order[v])))] << k
               for k, (u, v) in enumerate(edges(n)))


def factor_representation(n, mask, colors, radicand):
    neighbors = [set() for _ in range(n)]
    for k, (u, v) in enumerate(edges(n)):
        if bool(mask >> k & 1) ^ bool(colors[u] and colors[v]):
            neighbors[u].add(v)
            neighbors[v].add(u)
    if any(len(row) > 2 for row in neighbors):
        return False

    covered = set()
    for start in range(n):
        if start in covered or len(neighbors[start]) > 1:
            continue
        word = []
        prev, current = None, start
        while True:
            covered.add(current)
            word.append(colors[current])
            following = neighbors[current] - {prev}
            if not following:
                break
            prev, current = current, next(iter(following))
        if not (is_factor(tuple(word), radicand) or is_factor(tuple(reversed(word)), radicand)):
            return False
    return len(covered) == n  # Any remaining component is a cycle.


def check_small_graphs(radicand):
    total = 0
    for n in range(6):
        ordered = {literal_fold(p, radicand) for p in combinations(range(24), n)}
        literal = {relabel(n, mask, pi) for mask in ordered for pi in permutations(range(n))}
        for mask in range(1 << len(edges(n))):
            recognized = any(factor_representation(n, mask, colors, radicand)
                             for colors in product((0, 1), repeat=n))
            assert recognized == (mask in literal), (radicand, n, mask)
            total += 1
    return total


def check_recovery():
    rng = Random(20261128)
    checks = 0
    for radicand in (3, 5):
        for _ in range(600):
            positions = sorted(rng.sample(range(45), rng.randrange(8, 32)))
            colors = {v for v, i in enumerate(positions) if bit(i, radicand)}
            if len(colors) < 6:
                continue
            mask = literal_fold(positions, radicand)
            degrees = [0] * len(positions)
            for k, (u, v) in enumerate(edges(len(positions))):
                if mask >> k & 1:
                    degrees[u] += 1
                    degrees[v] += 1
            assert colors == {v for v, deg in enumerate(degrees) if deg > 2}
            checks += 1
    return checks


if __name__ == "__main__":
    count = sum(check_small_graphs(d) for d in (3, 5))
    recovered = check_recovery()
    print(f"Folded forests: {count} labeled graph/slope membership checks, "
          f"{recovered} degree-recovery checks")
