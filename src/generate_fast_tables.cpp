// Two-level 4^n Hilbert-style tables from an arbitrary parent Gray sequence,
// using only GF(2)^n state (no 4^n lattice, no Boost graph).
//
// Notation (bitmasks in GF(2)^k):
//   - parent cube at step w:          h_w = gray[w]
//   - child entry corner (local):     ell_in[w]
//   - child exit direction index:     dir[w]  (0..k-1)
//   - child exit corner (local):      ell_out[w] = ell_in[w] XOR e_{dir[w]}
//   - parent transition dimension:    d_w where gray[w+1] = gray[w] XOR e_{d_w}
//
// Key “mismatch” state:
//   s_w := h_w XOR ell_in[w]   in GF(2)^k.
//
// Constraints equivalent to the exit-to-exit construction:
//   s_0 = 0,
//   s_{w+1} = s_w XOR e_{dir[w]},
//   (s_{w+1})_{d_w} = 1   for each parent step w,
//   s_{last} has Hamming weight 1 (so last-cube entry is adjacent to the finish corner).
//
// Once s_w is found:
//   ell_in[w] = gray[w] XOR s_w,
//   dir[w] = bit flipped from s_w to s_{w+1}, and for the last cube dir[last] = index of the 1-bit in s_last.

#include <cassert>
#include <cstdint>
#include <iostream>
#include <limits>
#include <optional>
#include <vector>

namespace hilbertgen_fast
{

    using u8 = std::uint8_t;
    using u32 = std::uint32_t;
    using i32 = std::int32_t;

    static inline int ctz32(u32 x)
    {
        assert(x != 0u);
        return __builtin_ctz(x);
    }
    static inline int popcount32(u32 x) { return __builtin_popcount(x); }
    static inline bool is_pow2(u32 x) { return x && ((x & (x - 1u)) == 0u); }

    static inline u32 brgc(u32 i) { return i ^ (i >> 1); }
    static std::vector<u32> make_brgc_seq(int k)
    {
        const u32 N = 1u << (u32)k;
        std::vector<u32> g(N);
        for (u32 w = 0; w < N; w++)
            g[w] = brgc(w);
        return g;
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

    // Returns empty Tables{} on failure/invalid input.
    static Tables build_tables_gf2(int k, const std::vector<u32> &gray_seq)
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

        for (u32 w = 0; w < m; w++)
        {
            std::fill(nxt.begin(), nxt.end(), 0);
            const u32 required = (u32)d[w];

            for (u32 s = 0; s < S; s++)
            {
                if (!cur[s])
                    continue;

                for (u32 a = 0; a < (u32)k; a++)
                {
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

        // Choose any reachable final mismatch state with Hamming weight 1.
        u32 s_last = std::numeric_limits<u32>::max();
        for (u32 s = 0; s < S; s++)
        {
            if (!cur[s])
                continue;
            if (popcount32(s) == 1)
            {
                s_last = s;
                break;
            }
        }
        if (s_last == std::numeric_limits<u32>::max())
            return {}; // should not happen for k>=2

        // Reconstruct s_w and dir[w] for w=0..N-2 from predecessor pointers.
        std::vector<u32> s(N, 0u);
        std::vector<u32> dir(N, 0u); // we'll fill all; last uses s_last's set bit

        s[N - 1u] = s_last;
        for (u32 w = N - 1u; w >= 1u; w--)
        {
            const i32 ps = pred_state[(size_t)w * (size_t)S + (size_t)s[w]];
            const i32 ax = pred_axis[(size_t)w * (size_t)S + (size_t)s[w]];
            if (ps < 0 || ax < 0)
                return {}; // unreachable/invalid chain
            s[w - 1u] = (u32)ps;
            dir[w - 1u] = (u32)ax;
        }

        // Last cube: its exit is the “finish corner” local mask == gray[last].
        // Since l_in_last XOR l_finish has weight 1, s_last has weight 1, and that set bit index is dir[last].
        dir[N - 1u] = (u32)ctz32(s_last);

        // Convert mismatch s_w back to child entry corners.
        t.child_entry.assign(N, 0u);
        t.child_dir.assign(N, 0u);
        for (u32 w = 0; w < N; w++)
        {
            t.child_entry[w] = t.gray[w] ^ s[w]; // ell_in[w] = h_w XOR s_w
            t.child_dir[w] = dir[w];
        }

        // Optional consistency checks (can be removed for speed).
        // 1) entry in first cube is the origin corner
        if (t.child_entry[0] != 0u)
            return {};
        // 2) each parent step satisfies the face constraint via s_{w+1}[d_w]=1
        for (u32 w = 0; w < m; w++)
        {
            const u32 required = (u32)d[w];
            const u32 sw1 = s[w + 1u];
            if (((sw1 >> required) & 1u) == 0u)
                return {};
        }
        // 3) last mismatch has weight 1
        if (popcount32(s_last) != 1)
            return {};

        return t;
    }

} // namespace hilbertgen_fast

// Example driver (optional).
int main()
{
    using namespace hilbertgen_fast;
    const int k = 3;

    const auto gray = make_brgc_seq(k);
    Tables t = build_tables_gf2(k, gray);
    if (t.gray.empty())
    {
        std::cerr << "failed\n";
        return 1;
    }

    std::cout << "k=" << k << "\n";
    for (u32 w = 0; w < (u32)t.gray.size(); w++)
    {
        std::cout << "w=" << w
                  << " h=" << t.gray[w]
                  << " entry=" << t.child_entry[w]
                  << " dir=" << (u32)t.child_dir[w]
                  << "\n";
    }
    return 0;
}
