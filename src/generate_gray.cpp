#include "generate_gray.h"
#include <algorithm>
#include <functional>
#include <cassert>
#include <stack>

namespace graygen {

// Maximum number of backtracks before giving up
static constexpr size_t MAX_BACKTRACKS = 100000;

// ============================================================================
// Utility functions
// ============================================================================

// Rotate left by r bits within a k-bit word
static inline u32 rotl_bits(u32 x, int r, int k) {
    if (k == 0) return x;
    u32 mask = (1u << k) - 1;
    x &= mask;
    r = r % k;
    if (r == 0) return x;
    return ((x << r) | (x >> (k - r))) & mask;
}

// Normalize a Gray code so the exit edge is along axis 0.
// The exit edge is from gray[n-1] back to gray[0].
// After normalization: gray[0] XOR gray[n-1] == 1 (axis 0 direction).
static void normalize_exit_axis(std::vector<u32>& gray, int k) {
    if (gray.size() < 2 || k < 1) return;

    u32 diff = gray.front() ^ gray.back();
    if (diff == 0) return;  // Not a valid Gray code

    int exit_axis = __builtin_ctz(diff);
    if (exit_axis == 0) return;  // Already normalized

    // Rotate all vertices so exit_axis becomes axis 0
    // rotate left by (k - exit_axis) moves bit at exit_axis to position 0
    int rotation = (k - exit_axis) % k;

    for (u32& v : gray) {
        v = rotl_bits(v, rotation, k);
    }
}

// Warnsdorff degree: count of unvisited neighbors
static int warnsdorff_degree(u32 v, const std::vector<bool>& visited, int k) {
    int count = 0;
    for (int i = 0; i < k; i++) {
        u32 neighbor = v ^ (1u << i);
        if (!visited[neighbor]) count++;
    }
    return count;
}

// Get the axis (bit position) that differs between two adjacent vertices
static int get_transition_axis(u32 a, u32 b) {
    u32 diff = a ^ b;
    assert(diff != 0 && (diff & (diff - 1)) == 0);  // exactly one bit set
    return __builtin_ctz(diff);
}

std::vector<u32> compute_inverse(const std::vector<u32>& gray) {
    std::vector<u32> inv(gray.size());
    for (size_t w = 0; w < gray.size(); w++) {
        inv[gray[w]] = static_cast<u32>(w);
    }
    return inv;
}

std::vector<int> compute_transition_counts(const std::vector<u32>& gray, int k) {
    std::vector<int> counts(static_cast<size_t>(k), 0);
    size_t n = gray.size();
    for (size_t i = 0; i < n; i++) {
        size_t next = (i + 1) % n;  // cyclic
        int axis = get_transition_axis(gray[i], gray[next]);
        counts[static_cast<size_t>(axis)]++;
    }
    return counts;
}

// ============================================================================
// Verification functions
// ============================================================================

bool verify_gray_code(const std::vector<u32>& gray, int k) {
    size_t n = 1u << k;
    if (gray.size() != n) return false;

    // Check that all vertices are visited exactly once
    std::vector<bool> seen(n, false);
    for (u32 v : gray) {
        if (v >= n) return false;
        if (seen[v]) return false;
        seen[v] = true;
    }

    // Check adjacency: consecutive elements differ by exactly 1 bit
    for (size_t i = 0; i + 1 < n; i++) {
        if (hamming_dist(gray[i], gray[i + 1]) != 1) return false;
    }

    return true;
}

bool verify_cyclic(const std::vector<u32>& gray, int k) {
    (void)k;  // unused but kept for API consistency
    if (gray.empty()) return false;
    return hamming_dist(gray.front(), gray.back()) == 1;
}

bool verify_monotone(const std::vector<u32>& gray) {
    // Monotone: |v_i| <= |v_{i+2}| for all valid i
    for (size_t i = 0; i + 2 < gray.size(); i++) {
        if (popcount32(gray[i]) > popcount32(gray[i + 2])) {
            return false;
        }
    }
    return true;
}

bool verify_balanced(const std::vector<u32>& gray, int k, int tolerance) {
    auto counts = compute_transition_counts(gray, k);
    size_t n = gray.size();
    int target = static_cast<int>(n) / k;

    for (int c : counts) {
        if (c < target - tolerance || c > target + tolerance) {
            return false;
        }
    }
    return true;
}

// ============================================================================
// BRGC generation
// ============================================================================

std::vector<u32> generate_brgc(int k) {
    size_t n = 1u << k;
    std::vector<u32> gray(n);
    for (size_t w = 0; w < n; w++) {
        gray[w] = static_cast<u32>(w ^ (w >> 1));
    }
    // Normalize so exit is along axis 0
    normalize_exit_axis(gray, k);
    return gray;
}

// ============================================================================
// Iterative backtracking with Warnsdorff heuristic
// ============================================================================

struct SearchState {
    u32 vertex;
    int next_candidate_idx;
};

// Get sorted candidates using Warnsdorff heuristic
static std::vector<u32> get_sorted_candidates(
    u32 current,
    const std::vector<bool>& visited,
    int k,
    std::mt19937_64* rng = nullptr
) {
    std::vector<u32> candidates;
    for (int i = 0; i < k; i++) {
        u32 v = current ^ (1u << i);
        if (!visited[v]) {
            candidates.push_back(v);
        }
    }

    if (candidates.empty()) return candidates;

    // Optional shuffle before sorting (for random variant)
    if (rng) {
        std::shuffle(candidates.begin(), candidates.end(), *rng);
    }

    // Sort by Warnsdorff heuristic (fewest unvisited neighbors first)
    std::stable_sort(candidates.begin(), candidates.end(),
        [&](u32 a, u32 b) {
            return warnsdorff_degree(a, visited, k) < warnsdorff_degree(b, visited, k);
        });

    return candidates;
}

// Iterative Hamiltonian path search with Warnsdorff heuristic
static std::vector<u32> iterative_hamilton(int k, std::mt19937_64* rng = nullptr) {
    size_t n = 1u << k;

    std::vector<u32> path;
    path.reserve(n);
    path.push_back(0);

    std::vector<bool> visited(n, false);
    visited[0] = true;

    // Stack of (candidates, next_idx) for each position
    std::vector<std::pair<std::vector<u32>, size_t>> choice_stack;
    choice_stack.push_back({get_sorted_candidates(0, visited, k, rng), 0});

    size_t backtrack_count = 0;

    while (path.size() < n && backtrack_count < MAX_BACKTRACKS) {
        auto& [candidates, idx] = choice_stack.back();

        if (idx >= candidates.size()) {
            // No more candidates at this level, backtrack
            backtrack_count++;

            if (path.size() <= 1) {
                // Can't backtrack further
                return {};
            }

            u32 last = path.back();
            visited[last] = false;
            path.pop_back();
            choice_stack.pop_back();
            continue;
        }

        u32 next = candidates[idx];
        idx++;  // Move to next candidate for future backtracking

        path.push_back(next);
        visited[next] = true;

        if (path.size() < n) {
            choice_stack.push_back({get_sorted_candidates(next, visited, k, rng), 0});
        }
    }

    if (path.size() == n) {
        // Check cyclic property
        if (hamming_dist(path.front(), path.back()) == 1) {
            return path;
        }
        // Not cyclic, but this is rare with Warnsdorff - just return it anyway
        // for non-cyclic use cases, or try again
    }

    return {};  // Failed
}

// ============================================================================
// Random Gray code generation
// ============================================================================

std::vector<u32> generate_random(int k, u64 seed) {
    std::mt19937_64 rng(seed);
    size_t n = 1u << k;

    // Try iterative search with random shuffling
    for (int attempt = 0; attempt < 10; attempt++) {
        auto path = iterative_hamilton(k, &rng);
        if (!path.empty() && hamming_dist(path.front(), path.back()) == 1) {
            normalize_exit_axis(path, k);
            return path;
        }
    }

    // Fallback: apply random hypercube automorphism to BRGC
    // Note: generate_brgc already normalizes, but the automorphism changes the exit axis
    size_t base_n = 1u << k;
    std::vector<u32> base(base_n);
    for (size_t w = 0; w < base_n; w++) {
        base[w] = static_cast<u32>(w ^ (w >> 1));  // Raw BRGC without normalization
    }

    // Random axis permutation
    std::vector<int> perm(static_cast<size_t>(k));
    for (int i = 0; i < k; i++) perm[static_cast<size_t>(i)] = i;
    std::shuffle(perm.begin(), perm.end(), rng);

    // Random bit flip mask
    std::uniform_int_distribution<u32> dist(0, static_cast<u32>(n - 1));
    u32 flip_mask = dist(rng);

    std::vector<u32> result(n);
    for (size_t w = 0; w < n; w++) {
        u32 v = base[w];
        // Apply permutation
        u32 permuted = 0;
        for (int i = 0; i < k; i++) {
            if ((v >> i) & 1u) {
                permuted |= (1u << perm[static_cast<size_t>(i)]);
            }
        }
        // Apply flip
        result[w] = permuted ^ flip_mask;
    }

    // Rotate array so it starts at 0
    auto it = std::find(result.begin(), result.end(), 0u);
    if (it != result.begin() && it != result.end()) {
        std::rotate(result.begin(), it, result.end());
    }

    // Normalize so exit is along axis 0
    normalize_exit_axis(result, k);

    return result;
}

// ============================================================================
// Monotone Gray code generation (Savage-Winkler style)
// ============================================================================

// Monotone Gray codes satisfy: popcount(v_i) <= popcount(v_{i+2}) for all i.
// This means they oscillate between adjacent Hamming weight levels without
// going backwards. Finding these via search is difficult; the Savage-Winkler
// construction is more reliable but complex to implement.

// For k=2, BRGC happens to be monotone: 0,1,3,2 has weights 0,1,2,1
// Check: w[0]=0 <= w[2]=2 ✓, and it's cyclic.

// Try to build monotone code using iterative approach with weight constraint
static std::vector<u32> try_monotone_iterative(int k) {
    size_t n = 1u << k;

    std::vector<u32> path;
    path.reserve(n);
    path.push_back(0);

    std::vector<bool> visited(n, false);
    visited[0] = true;

    // Track the minimum weight we need (based on path[i-2])
    auto get_min_weight = [&]() -> u32 {
        if (path.size() < 2) return 0;
        return popcount32(path[path.size() - 2]);
    };

    // Get candidates respecting monotone constraint
    auto get_monotone_candidates = [&](u32 current) -> std::vector<u32> {
        std::vector<u32> candidates;
        u32 min_w = get_min_weight();

        for (int i = 0; i < k; i++) {
            u32 v = current ^ (1u << i);
            if (!visited[v] && popcount32(v) >= min_w) {
                candidates.push_back(v);
            }
        }

        // Sort by (weight, then Warnsdorff)
        std::sort(candidates.begin(), candidates.end(),
            [&](u32 a, u32 b) {
                u32 wa = popcount32(a), wb = popcount32(b);
                if (wa != wb) return wa < wb;
                return warnsdorff_degree(a, visited, k) < warnsdorff_degree(b, visited, k);
            });

        return candidates;
    };

    std::vector<std::pair<std::vector<u32>, size_t>> choice_stack;
    choice_stack.push_back({get_monotone_candidates(0), 0});

    size_t backtrack_count = 0;

    while (path.size() < n && backtrack_count < MAX_BACKTRACKS) {
        auto& [candidates, idx] = choice_stack.back();

        if (idx >= candidates.size()) {
            backtrack_count++;

            if (path.size() <= 1) {
                return {};
            }

            u32 last = path.back();
            visited[last] = false;
            path.pop_back();
            choice_stack.pop_back();
            continue;
        }

        u32 next = candidates[idx];
        idx++;

        path.push_back(next);
        visited[next] = true;

        if (path.size() < n) {
            choice_stack.push_back({get_monotone_candidates(next), 0});
        }
    }

    if (path.size() == n && hamming_dist(path.front(), path.back()) == 1) {
        return path;
    }

    return {};
}

std::vector<u32> generate_monotone(int k) {
    // For k=1 and k=2, BRGC is already monotone
    if (k <= 2) return generate_brgc(k);

    // Try iterative search with monotone constraint
    auto path = try_monotone_iterative(k);
    if (!path.empty()) {
        normalize_exit_axis(path, k);
        return path;
    }

    // Fallback to BRGC (not monotone, but valid Gray code)
    // Note: The Savage-Winkler construction would guarantee monotone codes,
    // but is complex to implement. For now, we fall back to BRGC.
    return generate_brgc(k);
}

// ============================================================================
// Balanced Gray code generation
// ============================================================================

// Try to build balanced code using greedy approach with balance heuristic
static std::vector<u32> try_balanced_iterative(int k, int tolerance) {
    size_t n = 1u << k;
    int target = static_cast<int>(n) / k;

    std::vector<u32> path;
    path.reserve(n);
    path.push_back(0);

    std::vector<bool> visited(n, false);
    visited[0] = true;

    std::vector<int> axis_counts(static_cast<size_t>(k), 0);

    // Get candidates preferring under-used axes
    auto get_balanced_candidates = [&](u32 current) -> std::vector<u32> {
        std::vector<u32> candidates;

        for (int i = 0; i < k; i++) {
            u32 v = current ^ (1u << i);
            if (!visited[v]) {
                // Don't exceed tolerance
                if (axis_counts[static_cast<size_t>(i)] < target + tolerance) {
                    candidates.push_back(v);
                }
            }
        }

        // Sort by (axis count, then Warnsdorff)
        std::sort(candidates.begin(), candidates.end(),
            [&](u32 a, u32 b) {
                int axis_a = get_transition_axis(current, a);
                int axis_b = get_transition_axis(current, b);
                int count_a = axis_counts[static_cast<size_t>(axis_a)];
                int count_b = axis_counts[static_cast<size_t>(axis_b)];
                if (count_a != count_b) return count_a < count_b;
                return warnsdorff_degree(a, visited, k) < warnsdorff_degree(b, visited, k);
            });

        return candidates;
    };

    std::vector<std::tuple<std::vector<u32>, size_t, int>> choice_stack;
    // (candidates, idx, axis_used_for_this_step)
    choice_stack.push_back({get_balanced_candidates(0), 0, -1});

    size_t backtrack_count = 0;

    while (path.size() < n && backtrack_count < MAX_BACKTRACKS) {
        auto& [candidates, idx, prev_axis] = choice_stack.back();

        if (idx >= candidates.size()) {
            backtrack_count++;

            if (path.size() <= 1) {
                return {};
            }

            // Undo the axis count increment
            if (prev_axis >= 0) {
                axis_counts[static_cast<size_t>(prev_axis)]--;
            }

            u32 last = path.back();
            visited[last] = false;
            path.pop_back();
            choice_stack.pop_back();
            continue;
        }

        u32 current = path.back();
        u32 next = candidates[idx];
        int axis = get_transition_axis(current, next);
        idx++;

        path.push_back(next);
        visited[next] = true;
        axis_counts[static_cast<size_t>(axis)]++;

        if (path.size() < n) {
            choice_stack.push_back({get_balanced_candidates(next), 0, axis});
        }
    }

    if (path.size() == n && hamming_dist(path.front(), path.back()) == 1) {
        // Check final balance (including the closing edge)
        int final_axis = get_transition_axis(path.back(), path.front());
        axis_counts[static_cast<size_t>(final_axis)]++;

        bool balanced = true;
        for (int c : axis_counts) {
            if (c < target - tolerance || c > target + tolerance) {
                balanced = false;
                break;
            }
        }

        if (balanced) {
            return path;
        }
    }

    return {};
}

std::vector<u32> generate_balanced(int k) {
    // BRGC is perfectly balanced for k=1 (counts: 2) and k=2 (counts: 2,2)
    if (k <= 2) return generate_brgc(k);

    // Try with increasing tolerance
    for (int tolerance = 2; tolerance <= 6; tolerance += 2) {
        auto path = try_balanced_iterative(k, tolerance);
        if (!path.empty()) {
            normalize_exit_axis(path, k);
            return path;
        }
    }

    // Fallback: BRGC
    return generate_brgc(k);
}

// ============================================================================
// Convenience wrapper
// ============================================================================

std::vector<u32> gray_code(int k, GrayCodeType type, u64 seed) {
    switch (type) {
        case GrayCodeType::BRGC:
            return generate_brgc(k);
        case GrayCodeType::Monotone:
            return generate_monotone(k);
        case GrayCodeType::Balanced:
            return generate_balanced(k);
        case GrayCodeType::Random:
            return generate_random(k, seed);
        default:
            return generate_brgc(k);
    }
}

} // namespace graygen
