"""Compare the recognition primitives with literal subpatterns and inversion counts."""

from itertools import combinations, permutations
from decision import (StructuredText, contains_1324, direct_cuts, find_witness, image,
                      orient, oriented_witness, singleton_compatible, singleton_witness,
                      standardize)


def literal_patterns(word, length):
    return {standardize(chosen) for chosen in combinations(word, length)}


def inversions(word):
    return sum(a > b for a, b in combinations(word, 2))


def avoids_1324_words(max_length):
    """Insert successive maxima, stopping before a 132 in the earlier prefix."""
    stack = [()]
    while stack:
        w = stack.pop()
        yield w
        n = len(w)
        if n == max_length:
            continue
        last_site = n
        for k in range(2, n):
            if any((min(w[:j]) < w[k] < w[j]) for j in range(1, k)):
                last_site = k
                break
        stack.extend(w[:j] + (n + 1,) + w[j:] for j in range(last_site + 1))


def checked_certificate(p, w):
    h = len(p)
    assert h - 1 <= len(w) <= h + 2, (p, w)
    assert p not in literal_patterns(w, h) and not contains_1324(w), (p, w)
    grown = image(w)
    assert grown is not None and p in literal_patterns(grown, h), (p, w, grown)


def check_classification():
    # Discover newly created patterns by exhausting source hosts independently of their predicted sign.
    witnessed = {h: set() for h in range(2, 7)}
    sharp = (3, 6, 4, 2, 5, 1)
    inputs = 0
    for w in avoids_1324_words(8):
        n = len(w)
        f = image(w)
        if f is None:
            continue
        inputs += 1
        for h in range(max(2, n - 2), min(6, n + 1) + 1):
            new = literal_patterns(f, h) - literal_patterns(w, h)
            if n <= 7:
                assert sharp not in new
            witnessed[h].update(new)
    compared = 0
    for h in witnessed:
        for p in permutations(range(1, h + 1)):
            assert (not singleton_compatible(p)) == (p in witnessed[h]), p
            compared += 1
    sharp_host = (5, 8, 3, 4, 2, 6, 1, 7)
    assert image(sharp_host) == (5, 3, 9, 4, 2, 6, 1, 7, 8)
    checked_certificate(sharp, sharp_host)
    certificates = 0
    for p in avoids_1324_words(7):
        if len(p) < 2:
            continue
        w = singleton_witness(p)
        if w is not None:
            checked_certificate(p, w)
            certificates += 1
        if len(direct_cuts(p)) >= 2:
            continue
        for d in range(4):
            old = oriented_witness(orient(p, d), d >= 2)
            if old is not None:
                checked_certificate(p, orient(old, d))
                certificates += 1
    print(f"Compared {compared} singleton decisions with {inputs} actual injection inputs; "
          f"validated {certificates} explicit singleton and orientation witnesses.")


def check_table(max_length):
    totals = [0] * (max_length + 1)
    for p in avoids_1324_words(max_length):
        totals[len(p)] += singleton_compatible(p)
    published = [3, 12, 66, 675, 6599, 55875, 431491]
    assert totals[4:] == published[:max_length - 3], totals
    print("Exact compatibility counts for lengths 4 through", max_length, "=", totals[4:])


def main():
    tests = [p for r in range(5) for p in permutations(range(1, r + 1))]
    compared = 0
    domain = 0
    for n in range(8):
        images = set()
        for word in permutations(range(1, n + 1)):
            actual = {r: literal_patterns(word, r) for r in range(5)}
            if n <= 6:
                text = StructuredText.parse(word)
                if text is not None:
                    for p in tests:
                        assert text.contains(p) == (p in actual[len(p)]), (p, word)
                        compared += 1
            if (1, 3, 2, 4) in actual[4]:
                continue
            grown = image(word)
            boundary = {0, n - 1}
            if word:
                boundary.update((word.index(1), word.index(n)))
            after_deletion = any(direct_cuts(standardize(word[:i] + word[i + 1:]))
                                 for i in boundary if 0 <= i < n)
            assert (grown is not None) == bool(direct_cuts(word) or after_deletion)
            if grown is not None:
                assert len(grown) == n + 1 and inversions(grown) == inversions(word)
                assert (1, 3, 2, 4) not in literal_patterns(grown, 4)
                assert grown not in images
                images.add(grown)
                domain += 1
    long_identity = tuple(range(1, 1201))
    long_text = StructuredText.parse(long_identity)
    assert long_text.contains(long_identity) and not long_text.contains((2, 1))
    assert find_witness(()) is None
    assert find_witness(((),)) is None
    assert find_witness(((1, 3, 2, 4),)) is None
    assert find_witness(((2, 1),)) is None
    assert find_witness(((1, 2),)) is None
    for basis in (((1, 2, 4, 3),), ((2, 1, 4, 3),), ((2, 4, 1, 3),),
                  ((2, 4, 1, 3), (4, 3, 2, 1))):
        found = find_witness(basis)
        assert found is not None, basis
        old, new, forbidden = found
        assert image(old) == new and forbidden in literal_patterns(new, len(forbidden))
        assert all(p not in literal_patterns(old, len(p)) for p in basis)
    print(f"Checked {compared} pattern-containment queries, {domain} source injection images, "
          "and four explicit incompatibility witnesses.")


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--table", action="store_true", help="reproduce source Table 2 through length ten")
    args = parser.parse_args()
    if args.table:
        check_table(10)
    else:
        main()
        check_classification()
        check_table(8)
