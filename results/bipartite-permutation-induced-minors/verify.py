"""Test the width-word theorem against literal deletions and edge contractions."""

from itertools import product


def blowup(widths):
    rows = [i for i, width in enumerate(widths) for _ in range(width)]
    return tuple(sum(1 << j for j, other in enumerate(rows) if abs(row - other) == 1)
                 for row in rows)


def remove_vertex(graph, vertex):
    low = (1 << vertex) - 1
    return tuple((neighbors & low) | ((neighbors >> (vertex + 1)) << vertex)
                 for i, neighbors in enumerate(graph) if i != vertex)


def contract_edge(graph, u, v):
    # Merge into u, erase loops, and renumber after deleting v.
    merged = list(graph)
    merged[u] = (graph[u] | graph[v]) & ~((1 << u) | (1 << v))
    for w, neighbors in enumerate(graph):
        if w != u and neighbors >> v & 1:
            merged[w] |= 1 << u
    return remove_vertex(merged, v)


def operations(graph):
    for u, neighbors in enumerate(graph):
        yield remove_vertex(graph, u)
        for v in range(u + 1, len(graph)):
            if neighbors >> v & 1:
                yield contract_edge(graph, u, v)


def width_word(graph):
    # An unlabelled path with at least four rows has distinct neighborhoods
    # at its different rows. Recover it by identifying equal open neighborhoods.
    twins = {}
    for i, neighbors in enumerate(graph):
        twins.setdefault(neighbors, []).append(i)
    groups = list(twins.values())
    quotient = [[j for j, other in enumerate(groups)
                 if graph[group[0]] >> other[0] & 1]
                for group in groups]
    ends = [i for i, row in enumerate(quotient) if len(row) == 1]
    if len(groups) < 4 or len(ends) != 2 or any(len(row) not in (1, 2) for row in quotient):
        return None
    prev, current = None, ends[0]
    widths = []
    while True:
        widths.append(len(groups[current]))
        following = [v for v in quotient[current] if v != prev]
        if not following:
            break
        prev, current = current, following[0]
    if len(widths) != len(groups):
        return None
    return min(tuple(widths), tuple(reversed(widths)))


def fits(target, host):
    inside = target[1:-1]
    return any(all(a <= b for a, b in zip(oriented, host[start:start+len(inside)]))
               for oriented in (inside, inside[::-1])
               for start in range(1, len(host) - len(inside)))


def check():
    words = {(2,) + inner + (2,) for length in range(2, 5)
             for inner in product((2, 3), repeat=length)}
    words = {min(x, x[::-1]) for x in words if sum(x) <= 14}
    antichain = {(2, 3) + (2,) * gap + (3, 2) for gap in (2, 3)}
    words |= antichain
    pairs = negatives = states = 0
    for host in sorted(words):
        frontier = {blowup(host)}
        for depth in range(3):
            states += len(frontier)
            obtained = {width_word(graph) for graph in frontier}
            for target in words:
                if sum(target) != sum(host) - depth:
                    continue
                predicted = fits(target, host)
                assert (target in obtained) == predicted, (target, host)
                if target in antichain and host in antichain:
                    assert predicted == (target == host)
                pairs += 1
                negatives += not predicted
            if depth < 2:
                frontier = {child for graph in frontier for child in operations(graph)}
    print(f"Induced minors: {pairs} width-word pairs, {negatives} negative, "
          f"{states} graph states reached by literal operations")


if __name__ == "__main__":
    check()
