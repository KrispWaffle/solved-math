"""Compare prescribed pattern occurrences with empty-to-empty exclusion walks."""

from collections import defaultdict
from functools import cache


def packing_extensions(height, width):
    # For the odd-then-even pattern each sorted rank locates a physical position.
    n = height * width
    predecessors = [0] * n
    for occurrence in range(width - 1):
        start = occurrence * height
        chain = [
            start + level + offset
            for level in range(height)
            for offset in (0, height)
        ]
        for a, b in zip(chain, chain[1:]):
            predecessors[b] |= 1 << a

    @cache
    def extensions(used):
        if used == (1 << n) - 1:
            return 1
        return sum(
            extensions(used | (1 << k))
            for k, required in enumerate(predecessors)
            if not used & (1 << k) and not required & ~used
        )

    return extensions(0)


def empty_returns(width, max_height):
    last = 1 << (width - 2)
    ways = {0: 1}
    result = [1]
    for step in range(1, width * max_height + 1):
        following = defaultdict(int)
        for state, count in ways.items():
            if not state & 1:
                following[state | 1] += count
            for k in range(width - 2):
                edge = 3 << k
                if state & edge == 1 << k:
                    following[state ^ edge] += count
            if state & last:
                following[state ^ last] += count
        ways = following
        if step % width == 0:
            result.append(ways[0])
    return result


def main():
    checks = 0
    for width in range(2, 12):
        max_height = min(10, 58 // width)
        returns = empty_returns(width, max_height)
        for height in range(2, max_height + 1):
            physical = packing_extensions(height, width)
            assert physical == returns[height], (height, width, physical, returns[height])
            checks += 1
    print(f"Matched {checks} exact packing counts to exclusion-walk returns.")


if __name__ == "__main__":
    main()
