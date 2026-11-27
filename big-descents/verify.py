"""Compare the tableau formula and the defining permutation sum in the F basis."""

from bisect import bisect_left
from collections import Counter, defaultdict
from itertools import permutations


def tableaux(size):
    """Generate standard tableaux as the sequence of cells containing 1, 2, ... ."""
    def grow(shape, cells):
        if len(cells) == size:
            yield tuple(shape), tuple(cells)
            return
        for row in range(len(shape) + 1):
            col = shape[row] if row < len(shape) else 0
            if row and col == shape[row - 1]:
                continue
            new_shape = shape.copy()
            if row == len(shape):
                new_shape.append(1)
            else:
                new_shape[row] += 1
            yield from grow(new_shape, [*cells, (row, col)])

    yield from grow([], [])


def transpose(shape):
    return tuple(sum(width > col for width in shape) for col in range(max(shape, default=0)))


def strict_elegant_fillings(outer, inner):
    """Count row- and column-strict fillings with row i bounded by i-1."""
    if len(inner) > len(outer) or any(a > b for a, b in zip(inner, outer)):
        return 0
    cells = [(row, col) for row, width in enumerate(outer)
             for col in range(inner[row] if row < len(inner) else 0, width)]
    values = {}

    def fill(index):
        if index == len(cells):
            return 1
        row, col = cells[index]
        lower = max(values.get((row - 1, col), 0), values.get((row, col - 1), 0)) + 1
        total = 0
        for value in range(lower, row + 1):
            values[row, col] = value
            total += fill(index + 1)
        values.pop((row, col), None)
        return total

    return fill(0)


def permutation_counts(n):
    counts = Counter()
    for word in permutations(range(n)):
        tails = []
        for value in word:
            place = bisect_left(tails, value)
            if place == len(tails):
                tails.append(value)
            else:
                tails[place] = value
        big_descents = tuple(i for i in range(1, n) if word[i - 1] > word[i] + 1)
        counts[len(tails), big_descents] += 1
    return counts


def verify(max_size):
    no_vertical_succession = Counter()
    for n in range(max_size + 1):
        schur_to_fundamental = defaultdict(Counter)
        for shape, cells in tableaux(n):
            pairs = list(zip(cells, cells[1:]))
            descents = tuple(i for i, (a, b) in enumerate(pairs, 1) if a[0] < b[0])
            schur_to_fundamental[shape][descents] += 1
            if all(b != (a[0] + 1, a[1]) for a, b in pairs):
                no_vertical_succession[shape] += 1

        predicted = Counter()
        for outer, descent_counts in schur_to_fundamental.items():
            for inner, multiplicity in no_vertical_succession.items():
                coefficient = multiplicity * strict_elegant_fillings(transpose(outer), transpose(inner))
                if coefficient:
                    width = max(inner, default=0)
                    for descents, count in descent_counts.items():
                        predicted[width, descents] += coefficient * count

        actual = permutation_counts(n)
        assert predicted == actual, (n, actual - predicted, predicted - actual)
        print(f"n={n}: all fundamental coefficients match for each exact LIS length")


if __name__ == "__main__":
    verify(9)
