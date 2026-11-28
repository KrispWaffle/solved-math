"""Compare the partition formula, minimum-insertion histories and literal avoiders."""
from collections import Counter
from itertools import combinations, permutations


def partition_formula(bound):
    # Scan each prospective marked level. A run start contributes its level.
    states = {(-1, False, 0): 1}
    for c in range(1, bound + 1):
        following = Counter()
        for (last, previous_mark, weight), count in states.items():
            following[last, False, weight] += count
            start = 0 if previous_mark else c
            for u in range(last + 1, min(c, bound - weight - start + 1)):
                following[u, True, weight + start + u] += count
        states = following
    values = [0] * (bound + 1)
    for (_, _, weight), count in states.items():
        values[weight] += count
    for part in range(1, bound + 1):
        for weight in range(part, bound + 1):
            values[weight] += values[weight - part]
    return values


def finite_rows(bound, last_length):
    states = {(0, 0, 0): 1}
    for n in range(last_length + 1):
        values = [0] * (bound + 1)
        for (_, _, weight), count in states.items():
            values[weight] += count
        yield values
        if n == last_length:
            return
        following = Counter()
        for (a, b, weight), count in states.items():
            for slot in range(a, min(n, bound - weight) + 1):
                next_a, next_b = (slot + 1, b + 1) if slot < b else (a, slot)
                following[next_a, next_b, weight + slot] += count
        states = following


def literal_counts(n):
    values = [0] * (n*(n-1)//2 + 1)
    quads = list(combinations(range(n), 4))
    for w in permutations(range(n)):
        if any(w[a] < w[b] < w[d] < w[c] for a, b, c, d in quads):
            continue
        inversions = sum(x > y for i, x in enumerate(w) for y in w[i+1:])
        values[inversions] += 1
    return values


def main():
    bound = 45
    stable = partition_formula(bound)
    assert stable[:10] == [1, 2, 5, 10, 20, 37, 66, 114, 193, 317]
    compared = 0
    for n, row in enumerate(finite_rows(bound, bound + 7)):
        if n <= 8:
            literal = literal_counts(n)
            assert row[:len(literal)] == literal and not any(row[len(literal):]), n
        for k in range(min(bound + 1, n - 1)):
            assert row[k] == stable[k], (n, k, row[k], stable[k])
            compared += 1
    print(f"Checked {compared} stable coefficients against length-bounded insertion, "
          "all permutations through length eight, and the ten published terms.")


if __name__ == '__main__':
    main()
