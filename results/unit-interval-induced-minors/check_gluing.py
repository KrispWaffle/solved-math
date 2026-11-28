"""Enumerate local minor models on endpoint diagrams and check their global union."""

from dataclasses import dataclass
from functools import cache
from itertools import combinations, product


@dataclass(frozen=True)
class Diagram:
    starts: tuple
    ends: tuple
    active: tuple


def diagrams(order):
    events = range(1, 2 * order + 1)
    for starts in combinations(events, order):
        ends = tuple(event for event in events if event not in starts)
        if any(left > right for left, right in zip(starts, ends)):
            continue
        active = tuple(tuple(i for i in range(order) if starts[i] <= t < ends[i])
                       for t in range(2 * order + 1))
        yield Diagram(starts, ends, active)


@dataclass(frozen=True)
class Patch:
    diagram: Diagram
    left: int
    right: int

    def vertices(self):
        return tuple(i for i, (a, b) in enumerate(zip(self.diagram.starts, self.diagram.ends))
                     if a <= self.right and self.left < b)

    def ports(self, cut):
        return self.diagram.active[cut]

    def adjacent(self, x, y):
        starts, ends = self.diagram.starts, self.diagram.ends
        return x != y and max(starts[x], starts[y]) < min(ends[x], ends[y])

    def signature(self):
        vertices = self.vertices()
        edges = frozenset((i, j) for i, j in combinations(range(len(vertices)), 2)
                          if self.adjacent(vertices[i], vertices[j]))
        left = tuple(vertices.index(x) for x in self.ports(self.left))
        right = tuple(vertices.index(x) for x in self.ports(self.right))
        return len(vertices), edges, left, right

    def tags(self):
        p = len(self.ports(self.left))
        return (self.ports(self.left)[0] % p, self.ports(self.right)[0] % p) if p else ()

    def excursions(self):
        p = len(self.ports(self.left))
        cuts = [t for t in range(self.left, self.right + 1) if len(self.ports(t)) == p]
        return tuple(Patch(self.diagram, a, b) for a, b in zip(cuts, cuts[1:]))

    def trim(self):
        trimmed = Patch(self.diagram, self.left + 1, self.right - 1)
        assert self.vertices() == trimmed.vertices()
        return trimmed


@cache
def admissible(target, host):
    """Assign unused vertices and all possible owners directly on the two small graphs."""
    n, target_edges, left, right = target
    m, host_edges, host_left, host_right = host
    if n > m:
        return ()
    forced = {}
    for v, w in zip(left + right, host_left + host_right):
        if w in forced and forced[w] != v:
            return ()
        forced[w] = v
    free = [w for w in range(m) if w not in forced]
    models = []
    for values in product(range(-1, n), repeat=len(free)):
        owners = forced | dict(zip(free, values))
        bags = [{w for w, owner in owners.items() if owner == v} for v in range(n)]
        if not all(bags):
            continue
        contracted_edges = set()
        neighbors = {w: set() for w in range(m)}
        for x, y in host_edges:
            a, b = owners[x], owners[y]
            if min(a, b) >= 0 and a != b:
                contracted_edges.add(tuple(sorted((a, b))))
            elif a == b:
                neighbors[x].add(y)
                neighbors[y].add(x)
        if contracted_edges != target_edges:
            continue
        for bag in bags:
            reached = set()
            frontier = {next(iter(bag))}
            while frontier:
                reached.update(frontier)
                frontier = set().union(*(neighbors[w] for w in frontier)) - reached
            if reached != bag:
                break
        else:
            models.append(tuple(owners[w] for w in range(m)))
    return tuple(models)


def check_models(source, host):
    pieces, available = source.excursions(), host.excursions()
    if source.tags() != host.tags() or len(pieces) > len(available):
        return 0
    count = 0
    for indices in combinations(range(len(available)), len(pieces)):
        selected = [available[j] for j in indices]
        if any(x.tags() != y.tags() for x, y in zip(pieces, selected)):
            continue
        local = [admissible(x.trim().signature(), y.trim().signature())
                 for x, y in zip(pieces, selected)]
        for chosen in product(*local):
            owners = {}

            def assign(vertex, owner):
                assert vertex not in owners or owners[vertex] == owner
                owners[vertex] = owner

            for x, y, model in zip(pieces, selected, chosen):
                vertices = x.vertices()
                for vertex, owner in zip(y.vertices(), model):
                    if owner >= 0:
                        assign(vertex, vertices[owner])
            gaps = [(host.left, selected[0].left, source.left)]
            gaps.extend((first.right, second.left, piece.right)
                        for first, second, piece in zip(selected, selected[1:], pieces))
            gaps.append((selected[-1].right, host.right, source.right))
            for a, b, cut in gaps:
                ports = source.ports(cut)
                if ports:
                    by_color = {v % len(ports): v for v in ports}
                    for w in Patch(host.diagram, a, b).vertices():
                        assign(w, by_color[w % len(ports)])
            # Check the completed model independently of the decomposition.
            for a, b in ((source.left, host.left), (source.right, host.right)):
                assert tuple(owners[w] for w in host.ports(b)) == source.ports(a)
            bags = {v: {w for w, owner in owners.items() if owner == v} for v in source.vertices()}
            for bag in bags.values():
                assert bag
                reached = {next(iter(bag))}
                for _ in range(len(bag)):
                    reached |= {v for v in bag if any(host.adjacent(v, w) for w in reached)}
                assert reached == bag
            for i, j in combinations(bags, 2):
                assert source.adjacent(i, j) == any(host.adjacent(x,y) for x in bags[i] for y in bags[j])
            count += 1
    return count


def check_gluing():
    levels = [[] for _ in range(4)]
    for order in range(1, 6):
        for diagram in diagrams(order):
            for a, b in combinations(range(2 * order + 1), 2):
                p = len(diagram.active[a])
                if p < len(levels) and len(diagram.active[b]) == p and all(
                        len(state) >= p for state in diagram.active[a:b+1]):
                    levels[p].append(Patch(diagram, a, b))
    total = sum(check_models(source, host) for level in levels for source in level for host in level)
    assert total == 67126
    print(f"Separator gluing: {sum(map(len, levels))} rooted patches, {total} checked global models")
