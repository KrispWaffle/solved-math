"""Compare the insertion recurrence with deletion and bar orientation on actual words."""

from collections import Counter
from itertools import combinations
from math import comb


def words(k, missing):
    current = [()]
    for j in range(1, k + 1):
        blocks = [(2*j, 2*j)]
        if j not in missing:
            blocks.insert(0, (2*j-1,))
        for block in blocks:
            current = [p[:v] + block + p[v:] for p in current for v in range(len(p) + 1)]
    return current


def descents(word):
    return sum(a > b for a, b in zip(word, word[1:]))


def active(word, k):
    result = {}
    for j in range(1, k + 1):
        u, v = word.index(2*j), len(word) - 1 - word[::-1].index(2*j)
        if u > 0 and word[u-1] == 2*j-1:
            result[j] = "left"
        elif v+1 < len(word) and word[v+1] == 2*j-1:
            result[j] = "right"
    return result


def insert(p, length):
    result = Counter()
    for d, count in p.items():
        result[d] += (d + 1) * count
        if length > d:
            result[d + 1] += (length - d) * count
    return result


def recurrence(k):
    old = [Counter({0: 1})]
    for j in range(1, k + 1):
        new = []
        for i in range(j + 1):
            length = 3*j - 2 - i
            inherited = insert(old[i], length - 1) if i < j else Counter()
            deleted = old[i-1] if i else Counter()
            new.append(insert(inherited + deleted, length))
        old = new
    return old


def check(k):
    direct = [Counter() for _ in range(k + 1)]
    for i in range(k + 1):
        for missing in combinations(range(1, k + 1), i):
            direct[i].update(descents(w) for w in words(k, missing))
    via_bonds = [Counter() for _ in range(k + 1)]
    for word in words(k, set()):
        orientations = active(word, k)
        if "right" in orientations.values():
            continue
        d, b = descents(word), len(orientations)
        for missing in range(b + 1):
            for right in range(b - missing + 1):
                via_bonds[missing][d + right] += comb(b, missing) * comb(b - missing, right)
    assert via_bonds == direct == recurrence(k)


if __name__ == "__main__":
    for k in range(5):
        check(k)
    print("All descent coefficients agree for the direct, insertion, and canonical-word counts at k=0,...,4.")
