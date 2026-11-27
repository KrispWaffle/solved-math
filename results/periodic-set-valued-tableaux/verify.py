"""Compare physical surjective words with a width-bounded outline transfer."""
from collections import defaultdict
from itertools import product
from math import comb, factorial


def heights(bits):
    profile = [0]
    for bit in bits:
        profile.append(profile[-1] - bit)
    return tuple(profile)


def physical_counts(cells, max_excess):
    """Append any physical cell except a strict predecessor of an earlier cell."""
    size = len(cells)
    forbidden = []
    for x, y in cells:
        forbidden.append(sum(1 << j for j, (u, v) in enumerate(cells)
                             if (x, y) != (u, v) and x <= u and y <= v))
    full = (1 << size) - 1
    counts = {0: 1}
    result = []
    for length in range(size + max_excess + 1):
        if length >= size:
            result.append(counts.get(full, 0))
        after = defaultdict(int)
        for used, ways in counts.items():
            for j, blocked in enumerate(forbidden):
                if not used & blocked:
                    after[used | (1 << j)] += ways
        counts = after
    return result


def moves(bits, visited):
    width = len(bits) + 1
    for bond in range(width):
        left = None if bond == 0 else bits[bond-1]
        right = None if bond+1 == width else bits[bond]
        if left != 0 and right != 1:
            new = list(bits)
            if left is not None:
                new[bond-1] = 0
            if right is not None:
                new[bond] = 1
            yield 1, tuple(new), visited | (1 << bond)
        if left != 1 and right != 0 and visited & (1 << bond):
            yield 0, bits, visited


def paths(start, max_size, max_excess):
    # Keep time layers separate. A self-loop represents a distinct repetition.
    counts = {(0, start, 0): 1}
    result = defaultdict(int)
    for length in range(max_size + max_excess + 1):
        after = defaultdict(int)
        for (size, bits, visited), ways in counts.items():
            result[size, length-size, bits] += ways
            for fresh, end, flags in moves(bits, visited):
                new_size = size + fresh
                if new_size <= max_size and length + 1 - new_size <= max_excess:
                    after[new_size, end, flags] += ways
        counts = after
    return result


def periodic_checks():
    cases = 0
    limit, excess = 8, 3
    for width in range(1, 6):
        outlines = list(product((0, 1), repeat=width-1))
        for start in outlines:
            p = heights(start)
            table = paths(start, limit, excess)
            for end in outlines:
                relative = heights(end)
                for offset in range(limit+1):
                    q = tuple(k+offset for k in relative)
                    if any(low > high for low, high in zip(p, q)):
                        continue
                    cells = [(k, k+i) for i in range(width) for k in range(p[i]+1, q[i]+1)]
                    size = len(cells)
                    if size > limit:
                        continue
                    for b, actual in enumerate(physical_counts(cells, excess)):
                        expected = table[size, b, end]
                        assert actual == expected, (p, q, b, actual, expected)
                        cases += 1
    print(f"{cases} physical word counts match the finite transfer, widths 1–5, up to 8 cells and excess 3")


def closed_forms():
    for width in (1, 2):
        start = (0,) * (width-1)
        table = paths(start, 20, 10)
        for size in range(width, 21, width):
            for b in range(11):
                assert table[size, b, start] == comb(size+b-1, b)
    # Width three has two paths around each intervening diamond.
    table = paths((0, 0), 21, 8)
    for k in range(1, 8):
        for b in range(9):
            expected = sum(comb(2*k+b-j, b-j) * (comb(k+j-2, j) if k>1 else int(j == 0))
                           * 2**j for j in range(b+1))
            assert table[3*k, b, (0, 0)] == 2**(k-1) * expected
    print("Chain binomial counts and 63 coefficients of the width-three rational formula match")


def printed_checks():
    for rows in range(1, 5):
        for width in range(1, 4):
            cells = [(i, j-i) for i in range(rows) for j in range(width)]
            assert all(c >= factorial(rows)**width for c in physical_counts(cells, 2))
    print("36 direct printed-coordinate counts satisfy the factorial lower bound")


if __name__ == "__main__":
    periodic_checks()
    closed_forms()
    printed_checks()
