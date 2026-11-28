"""Exact cross-checks using the Jacobi–Stirling and descent insertion recurrences."""

from fractions import Fraction
from math import comb, isqrt, prod

from check import recurrence


def diagonals(max_k, max_n):
    """Return [z^i] JS(n+k,n;z) indexed as table[n][k][i]."""
    table = []
    for n in range(max_n + 1):
        current = [[1]]
        for k in range(1, max_k + 1):
            row = table[n - 1][k].copy() if n else [0] * (k + 1)
            for i, value in enumerate(current[k - 1]):
                row[i] += n * n * value
                row[i + 1] += n * value
            current.append(row)
        table.append(current)
    return table


def amplitude(n, k, i):
    return prod(
        (Fraction(k * n * n, (n - h) * (k * n + (k - i) * h)) for h in range(1, n)),
        start=Fraction(1),
    )


def evaluation_sign(polynomial, point):
    """Sign of the source numerator t times the internal-descent polynomial."""
    degree = max(polynomial)
    value = polynomial[degree]
    scale = 1
    for d in reversed(range(degree)):
        scale *= point.denominator
        value = value * point.numerator + polynomial[d] * scale
    signed_value = value * point.numerator
    return (signed_value > 0) - (signed_value < 0)


def check_coefficients(table, max_k, max_n):
    count = 0
    for k in range(1, max_k + 1):
        for i in range(k + 1):
            previous = Fraction(1)
            for n in range(1, max_n + 1):
                c = table[n][k][i]
                b = Fraction(c, comb(k, i) * n ** (2 * k - i))
                a = amplitude(n, k, i)
                assert (1 - Fraction(2 * n * n, k)) * a <= b <= a, (k, i, n)
                if n > 1:
                    assert previous <= a <= previous * Fraction(n, n - 1) ** (n - 1)
                previous = a
                count += 1
    return count


def check_signs_and_normalization(table):
    signs = identities = 0
    for k in (16, 64, 144):
        row = recurrence(k)
        for i, polynomial in enumerate(row):
            d = 3 * k - i
            for n in range(1, len(table)):
                predicted = sum(
                    polynomial[m] * comb(n - 1 - m + d, d) for m in range(n)
                )
                assert table[n][k][i] == predicted, (k, i, n)
                identities += 1
        for i in sorted({0, k // 3, k // 2, k - 1, k}):
            for j in range(1, isqrt(k) // 4 + 1):
                c = Fraction(table[j][k][i], table[j + 1][k][i])
                center = Fraction(2 * j - 1, 2 * j + 1) ** (2 * k - i)
                for radius, sign in (
                    (center, (-1) ** j),
                    (c * Fraction(31, 32), (-1) ** j),
                    (c * Fraction(33, 32), (-1) ** (j + 1)),
                ):
                    assert evaluation_sign(row[i], -radius) == sign, (k, i, j, sign)
                    signs += 1
    return signs, identities


if __name__ == "__main__":
    table = diagonals(144, 8)
    bounds = check_coefficients(table, 72, 8)
    signs, identities = check_signs_and_normalization(table)
    print(f"Checked {bounds} coefficient bounds, {identities} source-series coefficients and {signs} exact signs.")
