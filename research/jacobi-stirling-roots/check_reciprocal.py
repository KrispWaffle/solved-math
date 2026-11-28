"""Check the reversed source series against the descent insertion recurrence."""

from fractions import Fraction
from math import comb

from check import recurrence


def elementary_diagonals(limit, extra):
    """Build [z^i] e_k(j(j+z) : 1 <= j <= n) for n=k,...,k+extra."""
    rows = [[1]] + [[0] * (k + 1) for k in range(1, limit + 1)]
    diagonals = {}
    for n in range(1, limit + extra + 1):
        for k in reversed(range(1, min(limit, n) + 1)):
            for i, value in enumerate(rows[k - 1]):
                rows[k][i] += n * n * value
                rows[k][i + 1] += n * value
            if n - k <= extra:
                diagonals[k, n - k] = rows[k].copy()
    return diagonals


def check_series(limit, extra):
    diagonals = elementary_diagonals(limit, extra)
    checked = 0
    for k in range(1, limit + 1):
        for i, polynomial in enumerate(recurrence(k)):
            m, degree = 3 * k - i, 2 * k - i - 1
            assert max(polynomial) == degree
            for s in range(extra + 1):
                value = sum(polynomial[degree - j] * comb(m + s - j, m)
                            for j in range(min(s, degree) + 1))
                assert value == diagonals[k, s][i], (k, i, s)
                checked += 1
    return checked


def check_scaled_signs():
    # Rational saddle approximations cover the endpoints, sparse deletions, and central columns.
    k = 96
    row = recurrence(k)
    checked = 0
    saddles = ((0, 0), (1, Fraction(1, 4)), (4, 1), (10, 3), (48, Fraction(2*k, 5)),
               (67, k), (78, 2*k), (95, 4500), (96, None))
    for i, r in saddles:
        tau = Fraction(1, k) if r is None else Fraction(1+r, k*(k+r))
        centers = [j if r is None else Fraction(j*(j+r), 1+r) for j in range(5)]
        for j in range(4):
            u = -tau * (centers[j] + centers[j+1]) / 2
            numerator, denominator_power = 0, 1
            for d in range(max(row[i]) + 1):
                numerator = numerator * u.numerator + row[i][d] * denominator_power
                denominator_power *= u.denominator
            assert (-1) ** j * numerator > 0, (k, i, u)
            checked += 1
    return checked


if __name__ == "__main__":
    print(f"Checked {check_series(20, 12)} reciprocal coefficients and "
          f"{check_scaled_signs()} exact signs at the large-root scale.")
