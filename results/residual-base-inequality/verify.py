"""Reproduce the finite census and compare with literal permutations at small lengths."""

import csv
from itertools import combinations, permutations
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
EQUALITIES = {
    (4, 3, 5, 8, 1, 2, 9, 11, 10, 6, 7),
    (5, 6, 2, 1, 3, 10, 11, 4, 7, 9, 8),
    (4, 3, 5, 7, 2, 8, 10, 1, 11, 13, 12, 9, 6),
    (8, 5, 2, 1, 3, 13, 4, 6, 12, 7, 9, 11, 10),
}


def has_cut(word):
    return any(max(word[:k]) < min(word[k:]) for k in range(1, len(word)))


def literal_row(n):
    budget = 3 * n - 4
    quads = list(combinations(range(n), 4))
    reduced = 0
    margins = []
    for word in permutations(range(n)):
        if any(y == x + 1 for x, y in zip(word, word[1:])):
            continue
        if any(word[i] < word[k] < word[j] < word[h] for i, j, k, h in quads):
            continue
        if sum(x > y for x, y in combinations(word, 2)) > budget:
            continue
        reduced += 1
        if has_cut(word):
            continue
        extremes = {0, n - 1, word.index(0), word.index(n - 1)}
        widths = [1] * n
        for i in extremes:
            if n == 2 or has_cut(word[:i] + word[i + 1:]):
                widths[i] = 2
        # Construct the inflated word and count inversions from the definition.
        inflated = []
        for i, x in enumerate(word):
            first = sum(widths[j] for j, y in enumerate(word) if y < x)
            inflated.extend(range(first, first + widths[i]))
        weight = sum(x > y for x, y in combinations(inflated, 2))
        margins.append(weight - 3 * len(inflated) + 15)
    return [str(x) for x in (n, budget, reduced, len(margins), min(margins),
                              margins.count(0), sum(x < 0 for x in margins))]


def main():
    lines = (ROOT / "census.tsv").read_text().splitlines()
    with tempfile.TemporaryDirectory() as tmp:
        for name in ("prefix_census", "census"):
            program = Path(tmp) / name
            subprocess.run(["c++", "-std=c++20", "-O3", str(ROOT / f"{name}.cpp"), "-o", program],
                           check=True)
            result = subprocess.run([program], capture_output=True, text=True, check=True)
            if result.stdout.splitlines() != lines[1:]:
                raise ValueError(f"{name} differs from the published per-length census")
    equalities = [tuple(map(int, line.split())) for line in result.stderr.splitlines()]
    if len(equalities) != len(EQUALITIES) or set(equalities) != EQUALITIES:
        raise ValueError(f"Unexpected equality cases {equalities}")
    rows = list(csv.reader(lines[1:], delimiter="\t"))
    if [int(row[0]) for row in rows] != list(range(2, 44)) or any(int(row[6]) for row in rows):
        raise ValueError("Missing length or counterexample to Meng's inequality")
    for row in rows[:7]:
        if literal_row(int(row[0])) != row:
            raise ValueError(f"Literal permutation enumeration disagrees at length {row[0]}")
    print(f"Meng 6.7: {sum(int(r[3]) for r in rows):,} indecomposable skeletons, "
          f"{len(equalities)} equalities, zero violations. Literal check through length 8.")


if __name__ == "__main__":
    main()
