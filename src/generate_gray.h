#pragma once

#include <cstdint>
#include <vector>
#include <random>

namespace graygen {

using u32 = uint32_t;
using u64 = uint64_t;

// Type of Gray code to generate
enum class GrayCodeType {
    BRGC,       // Binary Reflected Gray Code (baseline)
    Monotone,   // Savage-Winkler style: Hamming weight increases monotonically
    Balanced,   // Each axis flipped approximately equally
    Random      // Random valid cyclic Gray code
};

// Main generation functions
// k = dimension (2-7), returns vector of length 2^k
// gray[w] = vertex (bitmask) at position w in the path

std::vector<u32> generate_brgc(int k);
std::vector<u32> generate_monotone(int k);
std::vector<u32> generate_balanced(int k);
std::vector<u32> generate_random(int k, u64 seed);

// Convenience wrapper
std::vector<u32> gray_code(int k, GrayCodeType type, u64 seed = 0);

// Verification functions
bool verify_gray_code(const std::vector<u32>& gray, int k);
bool verify_cyclic(const std::vector<u32>& gray, int k);
bool verify_monotone(const std::vector<u32>& gray);
bool verify_balanced(const std::vector<u32>& gray, int k, int tolerance = 2);

// Utility functions
inline u32 popcount32(u32 x) { return static_cast<u32>(__builtin_popcount(x)); }
inline int hamming_dist(u32 a, u32 b) { return __builtin_popcount(a ^ b); }

std::vector<u32> compute_inverse(const std::vector<u32>& gray);
std::vector<int> compute_transition_counts(const std::vector<u32>& gray, int k);

} // namespace graygen
