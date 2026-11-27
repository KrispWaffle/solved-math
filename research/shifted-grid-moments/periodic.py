"""Exact transfers in the height of shifted grids with periodic subdivisions."""

from collections import deque
from fractions import Fraction


class LayerGraph:
    def __init__(self, windows, horizontal, vertical):
        if windows < 1 or not horizontal or len(horizontal) != len(vertical):
            raise ValueError("Supply a positive window count and one common nonempty period.")
        if min(*horizontal, *vertical) < 0:
            raise ValueError("Subdivision lengths must be nonnegative.")
        self.windows = windows
        self.horizontal = tuple(horizontal)
        self.vertical = tuple(vertical)
        self.block_length = len(horizontal) * (windows + 1) + windows * sum(
            h + v for h, v in zip(horizontal, vertical)
        )
        phases = []
        self.end_phases = []
        for level, (h, v) in enumerate(zip(horizontal, vertical)):
            phases.extend([("left", level)] + [("internal", level)] * h)
            phases.append(("right", level))
            self.end_phases.append(len(phases))
            phases.extend([("internal", level)] * v)
        self.phases = phases
        self.end_phases = [phase % len(phases) for phase in self.end_phases]

        start = (0,) * windows
        self.indices = {start: 0}
        self.edges = []
        self.classes = [[] for _ in range(self.block_length)]
        distances = [0]
        pending = deque([start])
        while pending:
            state = pending.popleft()
            index = self.indices[state]
            depth = distances[index]
            self.classes[depth % self.block_length].append(index)
            outgoing = []
            for dest in self.successors(state):
                if dest not in self.indices:
                    self.indices[dest] = len(distances)
                    distances.append(depth + 1)
                    pending.append(dest)
                other = self.indices[dest]
                assert (distances[other] - depth - 1) % self.block_length == 0
                outgoing.append(other)
            self.edges.append(outgoing)

    def successors(self, state):
        size = len(self.phases)
        for i, phase in enumerate(state):
            kind, level = self.phases[phase]
            if kind == "internal" or (kind == "left" and i == 0) or (
                kind == "right" and i == self.windows - 1
            ):
                dest = list(state)
                dest[i] = (phase + 1) % size
                yield tuple(dest)
            elif kind == "right" and self.phases[state[i + 1]] == ("left", level):
                dest = list(state)
                dest[i] = (phase + 1) % size
                dest[i + 1] = (dest[i + 1] + 1) % size
                yield tuple(dest)

    def packing(self, height):
        if height < 1:
            raise ValueError("The height must be positive.")
        p = len(self.horizontal)
        n = height * (self.windows + 1) + self.windows * (
            sum(self.horizontal[i % p] for i in range(height))
            + sum(self.vertical[i % p] for i in range(height - 1))
        )
        last = self.end_phases[(height - 1) % p]
        target = self.indices[(last,) * self.windows]
        counts = {0: 1}
        for _ in range(n):
            following = {}
            for i, count in counts.items():
                for j in self.edges[i]:
                    following[j] = following.get(j, 0) + count
            counts = following
        return counts[target]

    def growth_bounds(self, cycles):
        """Rational Collatz–Wielandt bounds per complete period of levels."""
        if cycles < 1:
            raise ValueError("At least one power of the return block is needed.")
        values = [1] * len(self.edges)
        zero_class = self.classes[0]
        for _ in range(cycles):
            previous = [values[i] for i in zero_class]
            for group in reversed(self.classes):
                for i in group:
                    values[i] = sum(values[j] for j in self.edges[i])
        ratios = [Fraction(values[i], old) for i, old in zip(zero_class, previous)]
        return min(ratios), max(ratios)
