// Exhaust all possible violations of Meng's base inequality by growing a
// reduced permutation inward from its two ends. See PROOF.md for each pruning rule.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

namespace {
using Mask = std::uint64_t;
constexpr int max_length = 43;

Mask bit(int value) { return Mask{1} << value; }
Mask below(int value) { return bit(value) - 1; }
int triangular(int value) { return value * (value + 1) / 2; }

int crop_bound(int length, int gaps) {
    int half = std::max(0, length - gaps) / 2;
    return triangular(half / 2) + triangular((half + 1) / 2);
}

class Census {
public:
    explicit Census(int length) : size(length), budget(3 * length - 4) {}

    void run() {
        visit(0, size, below(size), 0, size, -1);
        std::cout << size << '\t' << budget << '\t' << reduced << '\t' << indecomposable
                  << '\t' << (indecomposable ? std::to_string(least_margin) : "-")
                  << '\t' << equalities << '\t' << violations << '\n';
    }

private:
    int size, budget;
    std::array<int, max_length> word{};
    int reduced = 0, indecomposable = 0, least_margin = 1000, equalities = 0, violations = 0;

    // A sum cut is a proper prefix containing precisely its own lowest ranks.
    // omitted == size asks about the full skeleton.
    bool has_cut(int omitted) const {
        int length = size - (omitted < size);
        int deleted_value = omitted < size ? word[omitted] : size;
        int prefix_length = 0, largest = -1;
        for (int i = 0; i < size; ++i) {
            if (i == omitted) continue;
            int rank = word[i] - (word[i] > deleted_value);
            largest = std::max(largest, rank);
            ++prefix_length;
            if (prefix_length < length && largest == prefix_length - 1) return true;
        }
        return false;
    }

    void inspect(int inversions) {
        ++reduced;
        if (has_cut(size)) return;
        ++indecomposable;
        std::array<int, max_length> width{};
        int base_length = 0, base_inversions = inversions;
        for (int i = 0; i < size; ++i) {
            bool extreme = i == 0 || i == size - 1 || word[i] == 0 || word[i] == size - 1;
            width[i] = 1 + (extreme && (size == 2 || has_cut(i)));
            base_length += width[i];
            for (int j = 0; j < i; ++j) {
                if (word[j] > word[i]) base_inversions += width[i] * width[j] - 1;
            }
        }
        int margin = base_inversions - 3 * base_length + 15;
        least_margin = std::min(least_margin, margin);
        violations += margin < 0;
        if (margin != 0) return;
        ++equalities;
        std::vector<int> first(size, 1);
        for (int i = 0; i < size; ++i) {
            for (int j = 0; j < size; ++j) {
                if (word[j] < word[i]) first[i] += width[j];
            }
        }
        for (int i = 0; i < size; ++i) {
            for (int k = 0; k < width[i]; ++k) std::cerr << (i || k ? " " : "") << first[i] + k;
        }
        std::cerr << '\n';
    }

    bool has_pattern(int left, int right) const {
        std::array<int, max_length> smaller_before{};
        int smallest = size, largest = -1;
        for (int i = 0; i < size; ++i) {
            if (left <= i && i < right) continue;
            smaller_before[i] = smallest;
            smallest = std::min(smallest, word[i]);
        }
        for (int j = size - 1; j >= 0; --j) {
            if (left <= j && j < right) continue;
            for (int i = 0; i < j; ++i) {
                if (left <= i && i < right) continue;
                if (smaller_before[i] < word[j] && word[j] < word[i] && word[i] < largest)
                    return true;
            }
            largest = std::max(largest, word[j]);
        }
        return false;
    }

    void visit(int left, int right, Mask unused, int cost, int prefix_min, int suffix_max) {
        int length = right - left;
        if (length == 0) {
            inspect(cost);
            return;
        }
        int gaps = std::popcount(unused & ~(unused << 1)) - 1;
        if (cost + crop_bound(length, gaps) > budget) return;

        Mask middle = 0;
        if (prefix_min < suffix_max) middle = unused & ~below(prefix_min + 1) & below(suffix_max);
        if (std::popcount(middle & (middle << 1)) > length - std::popcount(middle)) return;

        bool from_left = left <= size - 1 - right;
        Mask choices = unused & ~middle;
        if (middle) {
            int next = from_left ? std::countr_zero(middle) : std::bit_width(middle) - 1;
            choices |= bit(next);
        }
        for (; choices; choices &= choices - 1) {
            int value = std::countr_zero(choices);
            if ((from_left || length == 1) && left > 0 && word[left - 1] + 1 == value) continue;
            if ((!from_left || length == 1) && right < size && value + 1 == word[right]) continue;
            int smaller = std::popcount(unused & below(value));
            int new_cost = cost + (from_left ? smaller : length - 1 - smaller);
            if (new_cost > budget) continue;
            word[from_left ? left : right - 1] = value;
            int next_left = left + from_left, next_right = right - !from_left;
            if (has_pattern(next_left, next_right)) continue;
            visit(next_left, next_right, unused ^ bit(value), new_cost,
                  from_left ? std::min(prefix_min, value) : prefix_min,
                  from_left ? suffix_max : std::max(suffix_max, value));
        }
    }
};
}  // namespace

int main() {
    for (int length = 2; length <= max_length; ++length) Census(length).run();
}
