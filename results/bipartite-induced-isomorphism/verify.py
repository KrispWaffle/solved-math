"""Check the reduction against induced subgraphs of the actual five-part path."""

from collections import Counter
from functools import cache
from itertools import combinations, combinations_with_replacement, permutations, product


def part_indices(mask):
    return [i for i in range(5) if mask & (1 << i)]


def different_components(left, right):
    return not ((left | left << 1 | left >> 1) & right)


@cache
def star_supports(sizes, leaves):
    """Enumerate the occupied parts and center of a star in a path blow-up."""
    supports = set()
    for center in range(5):
        if not sizes[center]:
            continue
        for mask in range(1, 32):
            parts = part_indices(mask)
            if all(abs(center - i) == 1 and sizes[i] for i in parts):
                if len(parts) <= leaves <= sum(sizes[i] for i in parts):
                    supports.add((1 << center) | mask)
    return supports


def placements(sizes, demands):
    eligible = [star_supports(sizes, d) for d in demands]
    options = {1 << i for i, supports in enumerate(eligible) if supports}
    for i, j in combinations(range(len(demands)), 2):
        if any(different_components(a, b) for a, b in product(eligible[i], eligible[j])):
            options.add((1 << i) | (1 << j))
    return options


def graph_decision(x, y, targets):
    left = tuple(3 * s for s in x)
    right = tuple(3 * s + 1 for s in y)
    base = 1 + max((3,) + left + right)
    multiplicity = Counter(targets)
    pairs = [(i, j, a + b) for i, a in enumerate(x) for j, b in enumerate(y)
             if a + b in multiplicity]
    counts = Counter(w for _, _, w in pairs)
    if sum(x) + sum(y) != sum(targets) or any(counts[w] < n for w, n in multiplicity.items()):
        return False
    blockers = [base + 3 * w + 1 for w, n in counts.items() for _ in range(n - multiplicity[w])]
    demands = left + right + tuple(blockers)
    used_sets = {0}
    for i, j, _ in pairs:
        a, b = left[i], right[j]
        options = placements((a, 1, base + min(a, b), 1, b), demands)
        used_sets |= {old | new for old in used_sets for new in options if not old & new}
    return (1 << len(demands)) - 1 in used_sets


def numerical_decision(x, y, targets):
    return any(sorted(a + b for a, b in zip(x, order)) == list(targets)
               for order in permutations(y))


def check_literal_subsets():
    """Recover all disjoint unions of large stars from literal induced adjacency."""
    checked = 0
    for a, common, b in product(range(1, 4), repeat=3):
        sizes = (a, 1, common, 1, b)
        parts = [i for i, size in enumerate(sizes) for _ in range(size)]
        adj = [sum(1 << j for j, q in enumerate(parts) if abs(p - q) == 1) for p in parts]
        actual = set()
        for mask in range(1, 1 << len(parts)):
            todo = mask
            stars = []
            while todo:
                component = todo & -todo
                reached = 0
                while reached != component:
                    reached = component
                    component |= sum_neighbors(adj, reached) & todo
                degrees = sorted((adj[i] & component).bit_count()
                                 for i in range(len(parts)) if component & (1 << i))
                leaves = len(degrees) - 1
                if leaves < 3 or degrees != [1] * leaves + [leaves]:
                    break
                stars.append(leaves)
                todo ^= component
            else:
                actual.add(tuple(sorted(stars)))
            checked += 1
        predicted = {(k,) for k in range(3, common + max(a, b) + 1)}
        predicted |= {tuple(sorted((i, j))) for i in range(3, a + 1) for j in range(3, b + 1)}
        if actual != predicted:
            raise AssertionError((sizes, actual ^ predicted))
    return checked


def sum_neighbors(adj, mask):
    result = 0
    while mask:
        bit = mask & -mask
        result |= adj[bit.bit_length() - 1]
        mask ^= bit
    return result


def main():
    literal = check_literal_subsets()
    checked = positive = 0
    for m in range(4):
        lists = list(combinations_with_replacement(range(1, 4), m))
        for x, y in product(lists, repeat=2):
            for targets in combinations_with_replacement(range(2, 7), m):
                want = numerical_decision(x, y, targets)
                if graph_decision(x, y, targets) != want:
                    raise AssertionError((x, y, targets, want))
                checked += 1
                positive += want
    if (checked, positive) != (4086, 219):
        raise AssertionError((checked, positive))
    print(f"{literal} literal induced subsets agree with the star capacities.")
    print(f"{checked} matching instances agree with induced packing, including {positive} positives.")


if __name__ == "__main__":
    main()
