"""Recognize compatibility of a finite basis for the prioritized Linusson–Verkama map."""

from dataclasses import dataclass
from itertools import combinations


def standardize(word):
    ranks = {value: i for i, value in enumerate(sorted(word), 1)}
    return tuple(ranks[value] for value in word)


def inverse(word):
    result = [0] * len(word)
    for i, value in enumerate(word, 1):
        result[value - 1] = i
    return tuple(result)


def reverse_complement(word):
    return tuple(len(word) + 1 - value for value in reversed(word))


def orient(word, direction):
    if direction >= 2:
        word = reverse_complement(word)
    return inverse(word) if direction % 2 else word


def direct_cuts(word):
    maximum = 0
    cuts = []
    for pos, value in enumerate(word[:-1], 1):
        maximum = max(maximum, value)
        if maximum == pos:
            cuts.append(pos)
    return cuts


def insert(word, position, value):
    shifted = tuple(x + (x >= value) for x in word)
    return shifted[:position] + (value,) + shifted[position:]


def image(word):
    """Compute f on a 1324-avoider in the domain, or return None for other domain shapes."""
    cuts = direct_cuts(word)
    if cuts:
        return insert(word, cuts[0], cuts[0] + 1)
    for direction in range(4):
        old = orient(word, direction)
        if not old:
            continue
        tail = standardize(old[1:])
        cuts = direct_cuts(tail)
        if cuts:
            grown = insert(tail, cuts[0], cuts[0] + 1)
            return orient(insert(grown, 0, old[0]), direction)
    return None


@dataclass(frozen=True)
class Node:
    length: int
    point: tuple = ()
    direct: bool = True
    left: int = -1
    right: int = -1


def separating_cut(points, start, stop):
    # Suffix bounds make every possible direct/skew cut test constant time.
    suffix_min = [0] * (stop - start)
    suffix_max = [0] * (stop - start)
    low = high = points[stop - 1][1]
    for i in range(stop - 1, start, -1):
        value = points[i][1]
        low, high = min(low, value), max(high, value)
        suffix_min[i - start], suffix_max[i - start] = low, high
    low = high = points[start][1]
    best = None
    for cut in range(start + 1, stop):
        value = points[cut - 1][1]
        low, high = min(low, value), max(high, value)
        direct = high < suffix_min[cut - start]
        if direct or low > suffix_max[cut - start]:
            distance = abs(2 * cut - start - stop)
            if best is None or distance < best[0]:
                best = distance, cut, direct
                if distance == 0:
                    break
    return best


def separating_tree(points):
    """Return a flat decomposition tree with parents preceding their children."""
    segments = [(0, len(points))]
    nodes = []
    for start, stop in segments:
        size = stop - start
        if size < 2:
            nodes.append(Node(size, points[start] if size else ()))
            continue
        split = separating_cut(points, start, stop)
        if split is None:
            # Every subword of a separable permutation is separable.
            return None
        _, cut, direct = split
        left = len(segments)
        segments.extend(((start, cut), (cut, stop)))
        nodes.append(Node(size, (), direct, left, left + 1))
    return tuple(nodes)


def tree_contains(tree, target, allowed):
    size = len(target)
    if not size:
        return True
    if size > tree[0].length:
        return False
    if size == tree[0].length:
        leaves = sorted(node.point for node in tree if node.length == 1)
        return (standardize(tuple(p[1] for p in leaves)) == standardize(target)
                and all(allowed(i, point) for i, point in enumerate(leaves)))

    tables = [None] * len(tree)
    for node_id in range(len(tree) - 1, -1, -1):
        node = tree[node_id]
        if node.length == 1:
            tables[node_id] = {(i, i + 1) for i in range(size) if allowed(i, node.point)}
            continue
        result = set()
        left, right = tables[node.left], tables[node.right]
        for start in range(size):
            for stop in range(start + 1, min(size, start + node.length) + 1):
                if (start, stop) in left or (start, stop) in right:
                    result.add((start, stop))
                    continue
                for cut in range(start + 1, stop):
                    if (start, cut) not in left or (cut, stop) not in right:
                        continue
                    u, v = target[start:cut], target[cut:stop]
                    ordered = max(u) < min(v) if node.direct else min(u) > max(v)
                    if ordered:
                        result.add((start, stop))
                        break
        tables[node_id] = result
        tables[node.left] = tables[node.right] = None
    return (0, size) in tables[0]


@dataclass(frozen=True)
class StructuredText:
    tree: tuple
    pivot: tuple = ()

    @classmethod
    def parse(cls, word):
        points = tuple(enumerate(word))
        tree = separating_tree(points)
        if tree is not None:
            return cls(tree)
        for i, pivot in enumerate(points):
            tree = separating_tree(points[:i] + points[i + 1:])
            if tree is not None:
                return cls(tree, pivot)
        return None

    def contains(self, target):
        if tree_contains(self.tree, target, lambda i, point: True):
            return True
        if not self.pivot:
            return False
        position, value = self.pivot
        for chosen, pivot_value in enumerate(target):
            rest = target[:chosen] + target[chosen + 1:]

            def permitted(i, point):
                return ((i < chosen) == (point[0] < position)
                        and (rest[i] < pivot_value) == (point[1] < value))

            if tree_contains(self.tree, rest, permitted):
                return True
        return False



def contains_1324(word):
    if len(word) < 4:
        return False
    from_left = [word[0]]
    for value in word[1:]:
        from_left.append(min(value, from_left[-1]))
    from_right = suffix_maxima(word)
    return any(from_left[j - 1] < word[k] < word[j] < from_right[k + 1]
               for j in range(1, len(word) - 2)
               for k in range(j + 1, len(word) - 1))


def suffix_maxima(word):
    maxima = list(word)
    for i in range(len(word) - 2, -1, -1):
        maxima[i] = max(word[i], maxima[i + 1])
    return maxima


def avoids_213(word):
    maxima = suffix_maxima(word)
    return all(not (word[j] < word[i] < maxima[j + 1])
               for j in range(1, len(word) - 1) for i in range(j))


def direct_sum(left, right):
    return left + tuple(len(left) + x for x in right)


def skew_sum(left, right):
    return tuple(len(right) + x for x in left) + right


def oriented_witness(q, late):
    """Construct a physical witness in first-deletion coordinates when this test succeeds."""
    h, first = len(q), q[0]
    tail = standardize(q[1:])
    tail_cuts = direct_cuts(tail)
    split = tail_cuts[-1] if tail_cuts else 0
    prefix, last = tail[:split], standardize(tail[split:])
    if first == h:
        if len(tail_cuts) < 2:
            return None
        guard = (2, 1) if late else (1,)
        old_tail = direct_sum(prefix[:-1], skew_sum(guard, last))
        return insert(old_tail, 0, len(old_tail) if late else len(old_tail) + 1)

    if late and first == h - 1:
        if len(tail_cuts) >= 2:
            final = skew_sum((1,), last) if len(last) >= 2 else (3, 2, 1)
            old_tail = direct_sum(prefix[:-1], final)
        else:
            if last[0] == len(last) or (not tail_cuts and not avoids_213(tail)):
                return None
            old_tail = direct_sum(prefix or (1,), skew_sum((1,), last))
        return insert(old_tail, 0, len(old_tail))

    cuts = direct_cuts(q)
    regular = (len(tail_cuts) > len(cuts)
               or (first > 1 and len(cuts) == 1 and first == cuts[0])
               or (1 < first < h and avoids_213(tail)))
    if not regular:
        return None
    old_tail = direct_sum(prefix or (1,), skew_sum(last, (1,)))
    return insert(old_tail, 0, first + (2 if tail_cuts else 3))


def singleton_witness(pattern):
    """Return an actual incompatible input, or None, in O(h²) time and O(h) space."""
    p = tuple(pattern)
    h = len(p)
    if sorted(p) != list(range(1, h + 1)):
        raise ValueError("expected a permutation of 1 through its length")
    if h < 2 or contains_1324(p):
        return None
    cuts = direct_cuts(p)
    if len(cuts) >= 2:
        j = cuts[0]
        return standardize(p[:j] + p[j + 1:])
    for direction in range(4):
        w = oriented_witness(orient(p, direction), direction >= 2)
        if w is not None:
            return orient(w, direction)
    return None


def singleton_compatible(pattern):
    """Decide compatibility of one forbidden pattern from its entries."""
    return singleton_witness(pattern) is None


def small_seeds(pattern):
    for removed in range(min(2, len(pattern)) + 1):
        for dropped in combinations(range(len(pattern)), removed):
            yield standardize(tuple(x for i, x in enumerate(pattern) if i not in dropped))


def witness_for(pattern, basis):
    """Search all bounded candidates for one possible output pattern."""
    last = len(pattern) + 18
    levels = [set() for _ in range(last + 1)]
    for seed in small_seeds(pattern):
        levels[len(seed)].add(seed)
    for n, level in enumerate(levels):
        for word in level:
            text = StructuredText.parse(word)
            if text is None or text.contains((1, 3, 2, 4)) or any(text.contains(p) for p in basis):
                continue
            if n + 1 >= len(pattern):
                grown = image(word)
                if grown is not None:
                    grown_text = StructuredText.parse(grown)
                    assert grown_text is not None
                    if grown_text.contains(pattern):
                        return word, grown, pattern
            if n < last:
                following = levels[n + 1]
                for i in range(n + 1):
                    for rank in range(1, n + 2):
                        following.add(insert(word, i, rank))
        level.clear()
    return None


def find_witness(basis):
    """Return (input, image, forbidden pattern), or None if the basis is compatible."""
    basis = tuple(dict.fromkeys(tuple(p) for p in basis))
    if any(sorted(p) != list(range(1, len(p) + 1)) for p in basis):
        raise ValueError("each forbidden pattern must be a permutation of 1 through its length")
    if () in basis:
        return None
    for pattern in basis:
        single = singleton_witness(pattern)
        if single is None:
            continue
        # The direct singleton certificate can also satisfy all the other restrictions.
        text = StructuredText.parse(single)
        if all(not text.contains(p) for p in basis):
            return single, image(single), pattern
        witness = witness_for(pattern, basis)
        if witness is not None:
            return witness
    return None
