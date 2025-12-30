// Fast Hilbert table generator using GF(2)^k mismatch-state DP.
//
// Features:
//   - Accepts arbitrary Gray codes from generate_gray.h
//   - Optional force_nonstandard to find non-Hamilton geometry
//   - Randomized candidate selection for diverse table generation
//   - Outputs to HDF5 using tables_hdf5.h API
//
// Usage:
//   ./generate_fast_tables --output FILE.h5 [options]
//     --output FILE.h5        Output HDF5 file (required)
//     --name NAME             Table family name (default: from gray type)
//     --index N               Index within family (default: 0)
//     --gray TYPE             Gray code: brgc, monotone, balanced, random (default: brgc)
//     --seed N                Random seed for Gray code and geometry (default: 12345)
//     --force-nonstandard     Try to find non-Hamilton child geometry

#include "generate_gray.h"

extern "C" {
#include "tables_hdf5.h"
}

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <limits>
#include <optional>
#include <random>
#include <string>
#include <vector>

namespace hilbertgen_fast
{

using u8 = std::uint8_t;
using u32 = std::uint32_t;
using u64 = std::uint64_t;
using i32 = std::int32_t;

static inline int ctz32(u32 x)
{
    assert(x != 0u);
    return __builtin_ctz(x);
}
static inline int popcount32(u32 x) { return __builtin_popcount(x); }
static inline bool is_pow2(u32 x) { return x && ((x & (x - 1u)) == 0u); }

static inline u32 brgc(u32 i) { return i ^ (i >> 1); }

static inline u32 trailing_ones(u32 x)
{
    u32 c = 0;
    while ((x & 1u) != 0u)
    {
        c++;
        x >>= 1u;
    }
    return c;
}

// Hamilton's (standard) child geometry for BRGC.
static inline u32 child_entry_std(u32 w)
{
    if (w == 0u)
        return 0u;
    return brgc((w - 1u) & ~1u);
}

static inline u32 child_dir_std(u32 w, u32 k)
{
    if (w == 0u)
        return 0u;
    if ((w & 1u) != 0u)
        return trailing_ones(w) % k;
    return trailing_ones(w - 1u) % k;
}

// Matches your file's Tables layout.
struct Tables
{
    int k = 0;
    std::vector<u32> gray;        // w -> vertex label (bitmask)
    std::vector<u32> gray_rank;   // vertex label -> w
    std::vector<u32> child_entry; // w -> entry corner bitmask (local)
    std::vector<u32> child_dir;   // w -> exit direction index (0..k-1)
};

// Check if tables match Hamilton's standard child geometry.
static bool is_standard(const Tables &t)
{
    const u32 N = (u32)t.gray.size();
    const u32 k = (u32)t.k;

    // Check if gray code is BRGC
    for (u32 w = 0; w < N; w++)
    {
        if (t.gray[w] != brgc(w))
            return false;
    }

    // Check child_entry and child_dir
    for (u32 w = 0; w < N; w++)
    {
        if (t.child_entry[w] != child_entry_std(w))
            return false;
        if (t.child_dir[w] != child_dir_std(w, k))
            return false;
    }
    return true;
}

// Build tables using GF(2)^k mismatch-state DP.
// Returns empty Tables{} on failure/invalid input.
//
// If force_nonstandard is true and the Gray code is BRGC, tries to find
// a non-Hamilton child geometry by iterating through all valid s_last candidates.
//
// geometry_seed: If non-zero, shuffle the candidate s_last values to get
// different valid child geometries for the same Gray code.
static Tables build_tables_gf2(int k, const std::vector<u32> &gray_seq,
                               bool force_nonstandard, u64 geometry_seed = 0)
{
    Tables t;
    t.k = k;

    if (k <= 0 || k > 31)
        return {};
    const u32 N = 1u << (u32)k; // number of child cubes
    const u32 S = 1u << (u32)k; // number of mismatch states (GF(2)^k)
    const u32 m = N - 1u;       // number of parent transitions

    if (gray_seq.size() != N)
        return {};
    if (gray_seq[0] != 0u)
        return {}; // start cube must be the origin cube

    t.gray = gray_seq;

    // Build inverse map and validate it's a permutation of [0,2^k).
    t.gray_rank.assign(N, std::numeric_limits<u32>::max());
    for (u32 w = 0; w < N; w++)
    {
        const u32 v = t.gray[w];
        if (v >= N)
            return {};
        if (t.gray_rank[v] != std::numeric_limits<u32>::max())
            return {};
        t.gray_rank[v] = w;
    }

    // k=1 is trivial.
    if (k == 1)
    {
        t.child_entry = {0u, 0u};
        t.child_dir = {0u, 0u};
        return t;
    }

    // Parent transition dimensions d_w: gray[w+1] = gray[w] XOR e_{d_w}.
    std::vector<u8> d(m, 0u);
    for (u32 w = 0; w < m; w++)
    {
        const u32 diff = t.gray[w] ^ t.gray[w + 1u];
        if (!is_pow2(diff))
            return {}; // not a Gray step
        d[w] = (u8)ctz32(diff);
        if ((int)d[w] >= k)
            return {};
    }

    // Layered DP over mismatch state s_w in GF(2)^k.
    //
    // pred_state[(w*S)+s] = predecessor mismatch state at layer w-1 (or -1 if unreachable)
    // pred_axis [(w*S)+s] = axis a used to go from predecessor to s (only valid if reachable and w>0)
    std::vector<i32> pred_state((size_t)N * (size_t)S, -1);
    std::vector<i32> pred_axis((size_t)N * (size_t)S, -1);

    std::vector<u8> cur((size_t)S, 0), nxt((size_t)S, 0);
    cur[0] = 1;
    pred_state[0 * (size_t)S + 0] = -2; // sentinel: start

    // Create shuffled orderings for states and axes if randomizing
    std::vector<u32> state_order(S);
    std::vector<u32> axis_order((size_t)k);
    for (u32 i = 0; i < S; i++) state_order[i] = i;
    for (u32 i = 0; i < (u32)k; i++) axis_order[i] = i;

    std::mt19937_64 rng(geometry_seed);

    for (u32 w = 0; w < m; w++)
    {
        std::fill(nxt.begin(), nxt.end(), 0);
        const u32 required = (u32)d[w];

        // Shuffle iteration order to get different predecessors recorded
        if (geometry_seed != 0)
        {
            std::shuffle(state_order.begin(), state_order.end(), rng);
            std::shuffle(axis_order.begin(), axis_order.end(), rng);
        }

        for (u32 si = 0; si < S; si++)
        {
            u32 s = state_order[si];
            if (!cur[s])
                continue;

            for (u32 ai = 0; ai < (u32)k; ai++)
            {
                u32 a = axis_order[ai];
                const u32 s2 = s ^ (1u << a);
                // Constraint: (s_{w+1})_{d_w} = 1
                if (((s2 >> required) & 1u) == 0u)
                    continue;

                if (!nxt[s2])
                {
                    nxt[s2] = 1;
                    pred_state[(size_t)(w + 1u) * (size_t)S + (size_t)s2] = (i32)s;
                    pred_axis[(size_t)(w + 1u) * (size_t)S + (size_t)s2] = (i32)a;
                }
            }
        }
        cur.swap(nxt);
    }

    // Collect all reachable final mismatch states with Hamming weight 1.
    std::vector<u32> candidates;
    for (u32 s = 0; s < S; s++)
    {
        if (!cur[s])
            continue;
        if (popcount32(s) == 1)
        {
            candidates.push_back(s);
        }
    }

    if (candidates.empty())
        return {}; // should not happen for k>=2

    // Shuffle candidates if a geometry seed is provided
    if (geometry_seed != 0)
    {
        std::mt19937_64 rng(geometry_seed + (u64)k); // Include k to vary per dimension
        std::shuffle(candidates.begin(), candidates.end(), rng);
    }

    // Lambda to reconstruct tables from a given s_last
    auto reconstruct = [&](u32 s_last) -> std::optional<Tables>
    {
        Tables result;
        result.k = k;
        result.gray = t.gray;
        result.gray_rank = t.gray_rank;

        // Reconstruct s_w and dir[w] for w=0..N-2 from predecessor pointers.
        std::vector<u32> s(N, 0u);
        std::vector<u32> dir(N, 0u);

        s[N - 1u] = s_last;
        for (u32 w = N - 1u; w >= 1u; w--)
        {
            const i32 ps = pred_state[(size_t)w * (size_t)S + (size_t)s[w]];
            const i32 ax = pred_axis[(size_t)w * (size_t)S + (size_t)s[w]];
            if (ps < 0 || ax < 0)
                return std::nullopt;
            s[w - 1u] = (u32)ps;
            dir[w - 1u] = (u32)ax;
        }

        // Last cube: its exit is the "finish corner" local mask == gray[last].
        dir[N - 1u] = (u32)ctz32(s_last);

        // Convert mismatch s_w back to child entry corners.
        result.child_entry.assign(N, 0u);
        result.child_dir.assign(N, 0u);
        for (u32 w = 0; w < N; w++)
        {
            result.child_entry[w] = result.gray[w] ^ s[w];
            result.child_dir[w] = dir[w];
        }

        // Consistency checks
        if (result.child_entry[0] != 0u)
            return std::nullopt;
        for (u32 w = 0; w < m; w++)
        {
            const u32 required = (u32)d[w];
            const u32 sw1 = s[w + 1u];
            if (((sw1 >> required) & 1u) == 0u)
                return std::nullopt;
        }
        if (popcount32(s_last) != 1)
            return std::nullopt;

        return result;
    };

    // Try each candidate s_last
    for (u32 s_last : candidates)
    {
        auto result = reconstruct(s_last);
        if (!result)
            continue;

        // If we need non-standard and this is standard, try next candidate
        if (force_nonstandard && is_standard(*result))
            continue;

        return *result;
    }

    // If force_nonstandard but all candidates are standard, return the first valid one
    // (this can happen if the Gray code itself forces a standard solution)
    if (force_nonstandard && !candidates.empty())
    {
        auto result = reconstruct(candidates[0]);
        if (result)
            return *result;
    }

    return {}; // no valid solution found
}

} // namespace hilbertgen_fast

static void print_usage(const char *prog)
{
    std::cerr << "Usage: " << prog << " --output FILE.h5 [options]\n";
    std::cerr << "  --output FILE.h5        Output HDF5 file (required)\n";
    std::cerr << "  --name NAME             Table family name (default: from gray type)\n";
    std::cerr << "  --index N               Index within family (default: 0)\n";
    std::cerr << "  --gray TYPE             Gray code: brgc, monotone, balanced, random (default: brgc)\n";
    std::cerr << "  --seed N                Random seed for 'random' type (default: 12345)\n";
    std::cerr << "  --force-nonstandard     Try to find non-Hamilton child geometry\n";
    std::cerr << "  --append                Append to existing file instead of truncating\n";
    std::cerr << "  --verbose               Print table details\n";
}

int main(int argc, char *argv[])
{
    using namespace hilbertgen_fast;

    // Parse command line arguments
    std::string output_file;
    std::string name;
    int index = 0;
    graygen::GrayCodeType gray_type = graygen::GrayCodeType::BRGC;
    u64 seed = 12345;
    bool force_nonstandard = false;
    bool append_mode = false;
    bool verbose = false;

    for (int i = 1; i < argc; i++)
    {
        std::string arg = argv[i];
        if (arg == "--output" && i + 1 < argc)
        {
            output_file = argv[++i];
        }
        else if (arg == "--name" && i + 1 < argc)
        {
            name = argv[++i];
        }
        else if (arg == "--index" && i + 1 < argc)
        {
            index = std::stoi(argv[++i]);
        }
        else if (arg == "--gray" && i + 1 < argc)
        {
            std::string type_str = argv[++i];
            if (type_str == "brgc")
            {
                gray_type = graygen::GrayCodeType::BRGC;
            }
            else if (type_str == "monotone")
            {
                gray_type = graygen::GrayCodeType::Monotone;
            }
            else if (type_str == "balanced")
            {
                gray_type = graygen::GrayCodeType::Balanced;
            }
            else if (type_str == "random")
            {
                gray_type = graygen::GrayCodeType::Random;
            }
            else
            {
                std::cerr << "Unknown gray type: " << type_str << "\n";
                print_usage(argv[0]);
                return 1;
            }
        }
        else if (arg == "--seed" && i + 1 < argc)
        {
            seed = std::stoull(argv[++i]);
        }
        else if (arg == "--force-nonstandard")
        {
            force_nonstandard = true;
        }
        else if (arg == "--append")
        {
            append_mode = true;
        }
        else if (arg == "--verbose" || arg == "-v")
        {
            verbose = true;
        }
        else if (arg == "--help" || arg == "-h")
        {
            print_usage(argv[0]);
            return 0;
        }
        else
        {
            std::cerr << "Unknown argument: " << arg << "\n";
            print_usage(argv[0]);
            return 1;
        }
    }

    // Validate required arguments
    if (output_file.empty())
    {
        std::cerr << "Error: --output is required\n";
        print_usage(argv[0]);
        return 1;
    }

    // Default name based on gray type
    if (name.empty())
    {
        switch (gray_type)
        {
        case graygen::GrayCodeType::BRGC:
            name = "brgc";
            break;
        case graygen::GrayCodeType::Monotone:
            name = "monotone";
            break;
        case graygen::GrayCodeType::Balanced:
            name = "balanced";
            break;
        case graygen::GrayCodeType::Random:
            name = "random";
            break;
        }
    }

    // Open or create HDF5 file
    hilbert_tables_ctx_t *ctx;
    if (append_mode)
    {
        ctx = hilbert_tables_open_rw(output_file.c_str());
    }
    else
    {
        ctx = hilbert_tables_create(output_file.c_str());
    }
    if (!ctx)
    {
        std::cerr << "Failed to open/create HDF5 file: " << output_file << "\n";
        return 1;
    }

    std::cout << "Generating tables for " << name << "/" << index << "...\n";

    // Generate tables for k=1..8
    for (int k = 1; k <= 8; k++)
    {
        auto gray = graygen::gray_code(k, gray_type, seed);
        Tables t = build_tables_gf2(k, gray, force_nonstandard, seed);

        if (t.child_entry.empty())
        {
            std::cerr << "Failed to build tables for k=" << k << "\n";
            hilbert_tables_close(ctx);
            return 1;
        }

        // Convert u32 vectors to uint8_t arrays
        const u32 size = 1u << k;
        std::vector<u8> gray8(size);
        std::vector<u8> gray_rank8(size);
        std::vector<u8> child_entry8(size);
        std::vector<u8> child_dir8(size);

        for (u32 w = 0; w < size; w++)
        {
            gray8[w] = (u8)t.gray[w];
            gray_rank8[w] = (u8)t.gray_rank[w];
            child_entry8[w] = (u8)t.child_entry[w];
            child_dir8[w] = (u8)t.child_dir[w];
        }

        // Write to HDF5
        int result = hilbert_tables_add(ctx, name.c_str(), index, k,
                                        gray8.data(), gray_rank8.data(),
                                        child_entry8.data(), child_dir8.data());
        if (result < 0)
        {
            std::cerr << "Failed to write tables for k=" << k << " to HDF5\n";
            hilbert_tables_close(ctx);
            return 1;
        }

        if (verbose)
        {
            bool std = is_standard(t);
            std::cout << "  k=" << k << " (standard=" << (std ? "yes" : "no") << ")\n";
            for (u32 w = 0; w < size; w++)
            {
                std::cout << "    w=" << w
                          << " gray=" << (u32)gray8[w]
                          << " entry=" << (u32)child_entry8[w]
                          << " dir=" << (u32)child_dir8[w]
                          << "\n";
            }
        }
        else
        {
            bool std = is_standard(t);
            std::cout << "  k=" << k << " done (standard=" << (std ? "yes" : "no") << ")\n";
        }
    }

    hilbert_tables_close(ctx);
    std::cout << "Wrote " << output_file << "\n";
    return 0;
}
