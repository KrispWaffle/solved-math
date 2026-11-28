// Independent left-to-right census, with graph connectivity after deleting an extreme.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <string>

namespace {
using Mask = std::uint64_t;
constexpr int limit = 43;
constexpr int infinity = 1000000;
using Word = std::array<int, limit + 1>;

Mask bit(int i) { return Mask{1} << i; }
Mask below(int i) { return bit(i) - 1; }
int triangular(int t) { return t * (t + 1) / 2; }

struct LowerBounds {
    Word reduced_132{}, reduced_1324{};
    LowerBounds() {
        Word without_final_max{};
        for (int n = 1; n <= limit; ++n) {
            without_final_max[n] = infinity;
            for (int right = 1; right < n; ++right) {
                int left = n - 1 - right;
                int cost = without_final_max[left] + reduced_132[right] + right * (n - right);
                without_final_max[n] = std::min(without_final_max[n], cost);
            }
            reduced_132[n] = std::min(without_final_max[n], without_final_max[n - 1]);
            int half = n / 2;
            reduced_1324[n] = triangular(half / 2) + triangular((half + 1) / 2);
        }
        // The subsequence argument gives a lower bound on length, not an exact length.
        for (int n = limit - 1; n >= 0; --n)
            reduced_132[n] = std::min(reduced_132[n], reduced_132[n + 1]);
    }
};

using Graph = std::array<Mask, limit>;

bool connected(const Graph& adjacency, Mask vertices) {
    Mask seen = 0, pending = vertices & -vertices;
    while (pending) {
        int i = std::countr_zero(pending);
        seen |= bit(i);
        pending ^= bit(i);
        pending |= adjacency[i] & vertices & ~seen;
    }
    return seen == vertices;
}

class PrefixCensus {
public:
    PrefixCensus(int n, const LowerBounds& bounds) : size(n), budget(3*n-4), bounds(bounds) {}

    void run() {
        Word ceiling;
        ceiling.fill(size);
        extend(0, below(size), 0, size, ceiling);
        std::cout << size << '\t' << budget << '\t' << reduced << '\t' << indecomposable
                  << '\t' << (indecomposable ? std::to_string(minimum) : "-")
                  << '\t' << equalities << '\t' << violations << '\n';
    }

private:
    int size, budget;
    const LowerBounds& bounds;
    Word word{};
    int reduced = 0, indecomposable = 0, minimum = infinity, equalities = 0, violations = 0;

    void inspect(int inversions) {
        ++reduced;
        Graph adjacency{};
        Mask extremes = bit(0) | bit(size - 1);
        for (int i = 0; i < size; ++i) {
            if (word[i] == 0 || word[i] == size - 1) extremes |= bit(i);
            for (int j = i + 1; j < size; ++j) {
                if (word[i] > word[j]) {
                    adjacency[i] |= bit(j);
                    adjacency[j] |= bit(i);
                }
            }
        }
        Mask vertices = below(size);
        if (!connected(adjacency, vertices)) return;
        ++indecomposable;
        Mask doubled = 0;
        for (; extremes; extremes &= extremes - 1) {
            int i = std::countr_zero(extremes);
            if (size == 2 || !connected(adjacency, vertices ^ bit(i))) doubled |= bit(i);
        }
        int base_length = size + std::popcount(doubled);
        for (Mask ends = doubled; ends; ends &= ends - 1) {
            int i = std::countr_zero(ends);
            inversions += std::popcount(adjacency[i]);
            inversions += std::popcount(adjacency[i] & (ends & (ends - 1)));
        }
        int margin = inversions - 3 * base_length + 15;
        minimum = std::min(minimum, margin);
        equalities += margin == 0;
        violations += margin < 0;
    }

    void extend(int pos, Mask unused, int cost, int prefix_min, const Word& ceiling) {
        if (!unused) {
            inspect(cost);
            return;
        }
        int length = size - pos;
        int groups = std::popcount(unused & ~(unused << 1));
        if (cost + bounds.reduced_1324[length - groups + 1] > budget) return;

        if (pos) {
            Mask upper = unused & ~below(prefix_min);
            if (upper) {
                int upper_groups = std::popcount(upper & ~(upper << 1));
                int unbroken = std::max(0, std::popcount(upper) - prefix_min - upper_groups + 1);
                if (cost + bounds.reduced_132[unbroken] > budget) return;
            }
        }
        int largest = std::bit_width(unused) - 1;
        int rank = 0;
        for (Mask options = unused; options; options &= options - 1, ++rank) {
            if (cost + rank > budget) break;
            int x = std::countr_zero(options);
            if (pos && word[pos - 1] + 1 == x) continue;
            if (largest > ceiling[x]) continue;
            word[pos] = x;
            Word next = ceiling;
            if (prefix_min < x) {
                Mask between = unused & below(x) & ~below(prefix_min + 1);
                for (; between; between &= between - 1) {
                    int y = std::countr_zero(between);
                    next[y] = std::min(next[y], x);
                }
            }
            extend(pos + 1, unused ^ bit(x), cost + rank, std::min(prefix_min, x), next);
        }
    }
};
}  // namespace

int main() {
    const LowerBounds bounds;
    for (int n = 2; n <= limit; ++n) PrefixCensus(n, bounds).run();
}
