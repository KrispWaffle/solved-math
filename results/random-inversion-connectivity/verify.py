"""Compare scanline cuts with graph connectivity defined by all vertex deletions."""

from itertools import permutations
from math import factorial


def inversion_graph(word):
    graph = [0] * len(word)
    for i, x in enumerate(word):
        for j in range(i):
            if word[j] > x:
                graph[i] |= 1 << j
                graph[j] |= 1 << i
    return graph


def connected(graph, keep):
    if not keep:
        return True
    pending = keep & -keep
    seen = pending
    while pending:
        point = pending & -pending
        pending ^= point
        neighbors = graph[point.bit_length() - 1] & keep & ~seen
        pending |= neighbors
        seen |= neighbors
    return seen == keep


def check(word):
    n = len(word)
    graph = inversion_graph(word)
    minimum = min(mask.bit_count() for mask in graph)
    if minimum == n - 1:
        return 0, 0, 0
    all_vertices = (1 << n) - 1
    connectivity = minimum
    minimum_cuts = set()
    for removed in range(all_vertices):
        size = removed.bit_count()
        if size <= connectivity and not connected(graph, all_vertices ^ removed):
            if size < connectivity:
                minimum_cuts.clear()
                connectivity = size
            minimum_cuts.add(removed)
    if not minimum_cuts:
        raise AssertionError(("missing literal separator", word))

    low = 0
    scans = set()
    two_point_obstructions = 0
    for j in range(1, n):
        low |= 1 << word.index(j - 1)
        for i in range(1, n):
            left = (1 << i) - 1
            sw = low & left
            ne = all_vertices & ~(low | left)
            if not sw or not ne:
                continue
            removed = left ^ low
            size = removed.bit_count()
            if size < connectivity:
                raise AssertionError(("scanline below connectivity", word, i, j))
            if size == connectivity:
                scans.add(removed)
            if size > minimum:
                continue
            count = sw.bit_count()
            for pos in range(i):
                if word[pos] < j and i - pos + j - word[pos] > 2 * count:
                    raise AssertionError(("corner bound", word, pos, i, j))
            gap = minimum - size
            if gap > 0:
                if count < gap + 1:
                    raise AssertionError(("insufficient vertices behind cut", word, i, j))
                if count == gap + 1:
                    block = tuple(range(j - 1, j - count - 1, -1))
                    if word[i - count:i] != block:
                        raise AssertionError(("forced decreasing block", word, i, j, gap))
                    if any(graph[h].bit_count() != minimum for h in range(i - count, i)):
                        raise AssertionError(("block has wrong degree", word, i, j, gap))
            if size < minimum and count == 2:
                if i < 2 or j < 2 or word[i-2:i] != (j-1, j-2):
                    raise AssertionError(("descending bond", word, i, j))
                two_point_obstructions += 1
    if scans != minimum_cuts:
        raise AssertionError(("literal and scanline cuts differ", word, minimum_cuts, scans))
    return int(connectivity < minimum), len(minimum_cuts), two_point_obstructions


def main():
    expected_exceptions = [0, 0, 1, 8, 63, 501, 4247]
    cuts = obstructions = 0
    for n, expected in enumerate(expected_exceptions, 2):
        exceptions = 0
        for word in permutations(range(n)):
            bad, separators, pairs = check(word)
            exceptions += bad
            cuts += separators
            obstructions += pairs
        if exceptions != expected:
            raise AssertionError((n, exceptions, expected))
        print(f"n={n}: {exceptions} of {factorial(n)} permutations have connectivity below minimum degree")
    if (cuts, obstructions) != (64493, 1882):
        raise AssertionError(("aggregate disagreement", cuts, obstructions))


if __name__ == "__main__":
    main()
