"""Exact block, parity and rational-witness checks for polynomial-growth classes."""

from itertools import permutations, product


def monotone_inflation(order, lengths, increasing):
    """Return the actual permutation and the predicted number of fixed points."""
    output = []
    predicted = 0
    for i, (length, up) in enumerate(zip(lengths, increasing)):
        u = len(output)
        v = sum(lengths[j] for j in range(len(order)) if order[j] < order[i])
        values = range(v, v + length)
        output.extend(values if up else reversed(values))
        if up:
            predicted += length if u == v else 0
        else:
            predicted += abs(v-u) <= length-1 and (v-u+length-1) % 2 == 0
    assert predicted == sum(i == x for i, x in enumerate(output))
    return tuple(output), predicted


def check_polynomial():
    boxes = 0
    for count in range(1, 4):
        for order in permutations(range(count)):
            for lengths in product(range(1, 5), repeat=count):
                for signs in product((False, True), repeat=count):
                    monotone_inflation(order, lengths, signs)
                    boxes += 1

    rational_slices = 0
    for b in range(1, 13):
        for a in range(b):
            for n in range(2*b+1, 2*b+9):
                low = {
                    tuple(range(t, n)) + tuple(reversed(range(t)))
                    for t in range(a+1)
                }
                high = {
                    tuple(range(n-t)) + tuple(reversed(range(n-t, n)))
                    for t in range(b-a+1)
                }
                assert low & high == {tuple(range(n))}
                assert len(low | high) == b
                assert sum(all(i != x for i, x in enumerate(pi)) for pi in low | high) == a
                rational_slices += 1

    for n in range(1, 31):
        # The class of a decreasing prefix skew-summed with an increasing suffix.
        members = {
            tuple(range(n-1, n-m-1, -1)) + tuple(range(n-m))
            for m in range(n+1)
        }
        expected = n-1 if n % 2 == 0 else (n-1)//2
        assert len(members) == n
        assert sum(all(i != x for i, x in enumerate(pi)) for pi in members) == expected

    for n in range(31):
        # Uniform compositions in one three-block box with an aligned middle block.
        centers = []
        for x in range(n+1):
            for y in range(n-x+1):
                z = n-x-y
                _, fixed = monotone_inflation((0, 1, 2), (2+x, 2+y, 2+z), (False, True, False))
                assert fixed == (2+y) + x % 2 + z % 2
                centers.append(y)
        assert 3 * sum(centers) == len(centers) * n
        assert 6 * sum(y*(y-1) for y in centers) == len(centers) * n*(n-1)
    return boxes, rational_slices


if __name__ == "__main__":
    print(check_polynomial())
