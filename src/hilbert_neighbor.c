/*
 * hilbert_neighbor.c
 *
 * Efficient computation of Hilbert indices for coordinate neighbors.
 *
 * Given p₀ = decode(h₀) and cached state, compute h₁ = encode(p₀ ± eₖ)
 * by reusing computations from the original decode.
 *
 * Key insight: levels ABOVE the highest changed bit are completely reusable.
 * We only need to recompute from s_top downward.
 */

#include <stdint.h>
#include <string.h>
#include <stdbool.h>

#define MAX_DIMS 32
#define MAX_LEVELS 64

typedef __uint128_t hindex_t;
typedef uint32_t coord_t;

/* Bit manipulation primitives */
static inline uint32_t gray_code(uint32_t i) { return i ^ (i >> 1); }
static inline uint32_t gray_decode(uint32_t g) {
    uint32_t i = 0;
    while (g) { i ^= g; g >>= 1; }
    return i;
}
static inline uint32_t mask_bits(int bits) { return bits > 0 ? ((1U << bits) - 1) : 0; }
static inline uint32_t rrotate(uint32_t x, int r, int bits) {
    if (bits <= 0) return x;
    r = r % bits;
    x &= mask_bits(bits);
    if (r == 0) return x;
    return ((x >> r) | ((x & ((1U << r) - 1)) << (bits - r))) & mask_bits(bits);
}
static inline uint32_t lrotate(uint32_t x, int r, int bits) {
    if (bits <= 0) return x;
    r = r % bits;
    x &= mask_bits(bits);
    if (r == 0) return x;
    return ((x << r) | (x >> (bits - r))) & mask_bits(bits);
}
static inline uint32_t T_transform(uint32_t e, int d, int bits, uint32_t b) {
    return rrotate((b ^ e) & mask_bits(bits), (d + 1) % bits, bits);
}
static inline int trailing_ones(uint32_t i) {
    int c = 0;
    while (i & 1) { c++; i >>= 1; }
    return c;
}
static inline uint32_t e_seq(int i) {
    if (i == 0) return 0;
    return gray_code(2 * ((i - 1) / 2));
}
static inline int d_seq(int bits, int i) {
    if (i == 0) return 0;
    if (i & 1) return trailing_ones(i) % bits;
    return trailing_ones(i - 1) % bits;
}

/* --------------------------------------------------------------------------
 * Full cached state for neighbor computations
 * -------------------------------------------------------------------------- */

typedef struct {
    int n;
    int mmax;
    int m[MAX_DIMS];
    int total_bits;

    /* Per-level cached data */
    int k[MAX_LEVELS + 1];               /* number of active axes */
    int A[MAX_LEVELS + 1][MAX_DIMS];     /* active axis list */
    int axis_pos[MAX_LEVELS + 1][MAX_DIMS]; /* position of each axis in A, or -1 */
    int bit_offset[MAX_LEVELS + 1];      /* bit position in h for this level's digit */

    /* State at entry to each level (before processing that level) */
    uint32_t e_entry[MAX_LEVELS + 1];
    int d_entry[MAX_LEVELS + 1];

    /* Digit values */
    uint32_t w[MAX_LEVELS + 1];

    /* The point and index */
    coord_t point[MAX_DIMS];
    hindex_t h;
} hilbert_neighbor_cache_t;

/* Axis ordering */
typedef struct { int axis; int exp; } axis_exp_t;

static void sort_axes_by_exp(const int *m, int n, int *order) {
    axis_exp_t items[MAX_DIMS];
    for (int i = 0; i < n; i++) { items[i].axis = i; items[i].exp = m[i]; }
    for (int i = 1; i < n; i++) {
        axis_exp_t key = items[i];
        int j = i - 1;
        while (j >= 0 && (items[j].exp > key.exp ||
               (items[j].exp == key.exp && items[j].axis > key.axis))) {
            items[j + 1] = items[j]; j--;
        }
        items[j + 1] = key;
    }
    for (int i = 0; i < n; i++) order[i] = items[i].axis;
}

static int get_active_axes(const int *m, int n, int s, const int *order, int *active) {
    int k = 0;
    for (int i = 0; i < n; i++) {
        int ax = order[i];
        if (m[ax] >= s) active[k++] = ax;
    }
    return k;
}

static void embed_state(const int *A_old, int k_old, const int *A_new, int k_new,
                        uint32_t e_old, int d_old, uint32_t *e_new, int *d_new) {
    int pos_new[MAX_DIMS];
    for (int j = 0; j < k_new; j++) pos_new[A_new[j]] = j;
    *e_new = 0;
    for (int j = 0; j < k_old; j++) {
        if ((e_old >> j) & 1) *e_new |= 1U << pos_new[A_old[j]];
    }
    *d_new = pos_new[A_old[d_old]];
}

/* --------------------------------------------------------------------------
 * Initialize cache by decoding h
 * -------------------------------------------------------------------------- */

void hilbert_neighbor_init(hilbert_neighbor_cache_t *cache, hindex_t h,
                           const int *m, int n) {
    memset(cache, 0, sizeof(*cache));
    if (n <= 0 || n > MAX_DIMS) return;

    cache->n = n;
    cache->h = h;
    memcpy(cache->m, m, n * sizeof(int));

    int mmax = 0;
    int total_bits = 0;
    for (int i = 0; i < n; i++) {
        if (m[i] > mmax) mmax = m[i];
        total_bits += m[i];
    }
    cache->mmax = mmax;
    cache->total_bits = total_bits;
    if (mmax == 0) return;

    /* Axis ordering */
    int order[MAX_DIMS];
    sort_axes_by_exp(m, n, order);

    /* Active axes and position maps for each level */
    for (int s = 1; s <= mmax; s++) {
        cache->k[s] = get_active_axes(m, n, s, order, cache->A[s]);

        /* Build reverse map: axis -> position in A[s], or -1 if not active */
        for (int ax = 0; ax < n; ax++) cache->axis_pos[s][ax] = -1;
        for (int j = 0; j < cache->k[s]; j++) {
            cache->axis_pos[s][cache->A[s][j]] = j;
        }
    }

    /* Compute bit offsets for each level's digit in h */
    int pos = total_bits;
    for (int s = mmax; s >= 1; s--) {
        pos -= cache->k[s];
        cache->bit_offset[s] = pos;
    }

    /* Decode with full state caching */
    int bit_pos = total_bits;
    uint32_t e = 0;
    int d = 0;

    for (int s = mmax; s >= 1; s--) {
        int *A = cache->A[s];
        int k = cache->k[s];

        /* Save entry state BEFORE processing this level */
        cache->e_entry[s] = e;
        cache->d_entry[s] = d;

        bit_pos -= k;
        uint32_t w = (uint32_t)((h >> bit_pos) & mask_bits(k));
        cache->w[s] = w;

        /* Decode bits */
        uint32_t l = gray_code(w);
        l = (lrotate(l, (d + 1) % k, k) ^ e) & mask_bits(k);

        for (int j = 0; j < k; j++) {
            int ax = A[j];
            cache->point[ax] |= ((l >> j) & 1) << (s - 1);
        }

        /* Update state for next level */
        e = e ^ lrotate(e_seq(w), (d + 1) % k, k);
        d = (d + d_seq(k, w) + 1) % k;

        if (s > 1 && cache->k[s - 1] > k) {
            uint32_t e_new; int d_new;
            embed_state(A, k, cache->A[s - 1], cache->k[s - 1], e, d, &e_new, &d_new);
            e = e_new; d = d_new;
        }
    }
}

/* --------------------------------------------------------------------------
 * Compute Hilbert index of a coordinate neighbor
 *
 * Given cached decode of h₀ → p₀, compute h₁ = encode(p₀ + delta * e_axis)
 * where delta is +1 or -1 and e_axis is the unit vector for axis `axis`.
 *
 * Returns the new index, or (hindex_t)-1 if the neighbor is out of bounds.
 * -------------------------------------------------------------------------- */

hindex_t hilbert_neighbor_index(const hilbert_neighbor_cache_t *cache,
                                int axis, int delta) {
    int n = cache->n;
    int mmax = cache->mmax;
    if (mmax == 0 || axis < 0 || axis >= n) return (hindex_t)-1;

    /* Check bounds */
    coord_t old_val = cache->point[axis];
    coord_t new_val;
    if (delta > 0) {
        if (old_val >= (1U << cache->m[axis]) - 1) return (hindex_t)-1;
        new_val = old_val + 1;
    } else {
        if (old_val == 0) return (hindex_t)-1;
        new_val = old_val - 1;
    }

    /*
     * Find which bits of coordinate `axis` change.
     * These determine which levels are affected.
     *
     * changed_bits = old_val ^ new_val
     * The highest set bit in changed_bits determines s_top.
     */
    uint32_t changed_bits = old_val ^ new_val;

    /* Find s_top: highest level where axis is active AND bit changes */
    int s_top = 0;
    for (int s = mmax; s >= 1; s--) {
        if (cache->axis_pos[s][axis] >= 0) {  /* axis is active at level s */
            if ((changed_bits >> (s - 1)) & 1) {  /* bit s-1 changed */
                s_top = s;
                break;
            }
        }
    }

    if (s_top == 0) {
        /* No active level affected - shouldn't happen if bounds check passed */
        return cache->h;
    }

    /*
     * Build the new index:
     * - Levels above s_top: copy digits from cache
     * - Levels s_top and below: recompute
     */

    hindex_t h_new = 0;

    /* Copy unchanged high digits */
    for (int s = mmax; s > s_top; s--) {
        h_new = (h_new << cache->k[s]) | cache->w[s];
    }

    /* Recompute from s_top down */
    uint32_t e = cache->e_entry[s_top];
    int d = cache->d_entry[s_top];

    for (int s = s_top; s >= 1; s--) {
        int k = cache->k[s];
        int *A = cache->A[s];

        e &= mask_bits(k);
        d = d % k;

        /* Build ℓ_s for the NEW point */
        uint32_t l = 0;
        for (int j = 0; j < k; j++) {
            int ax = A[j];
            coord_t coord_val = (ax == axis) ? new_val : cache->point[ax];
            l |= ((coord_val >> (s - 1)) & 1) << j;
        }

        /* Encode: w = gc⁻¹(T(ℓ)) */
        uint32_t l_t = T_transform(e, d, k, l);
        uint32_t w = gray_decode(l_t);

        h_new = (h_new << k) | w;

        /* Update state */
        e = e ^ lrotate(e_seq(w), (d + 1) % k, k);
        d = (d + d_seq(k, w) + 1) % k;

        if (s > 1 && cache->k[s - 1] > k) {
            uint32_t e_new; int d_new;
            embed_state(A, k, cache->A[s - 1], cache->k[s - 1], e, d, &e_new, &d_new);
            e = e_new; d = d_new;
        }
    }

    return h_new;
}

/*
 * Compute index delta: h_neighbor - h_original
 *
 * Note: This can be VERY large (up to 2^M - 1) or negative!
 * Returns as signed 128-bit by casting.
 */
__int128_t hilbert_neighbor_delta(const hilbert_neighbor_cache_t *cache,
                                  int axis, int delta) {
    hindex_t h_new = hilbert_neighbor_index(cache, axis, delta);
    if (h_new == (hindex_t)-1) return 0;  /* out of bounds */

    /* Signed difference */
    if (h_new >= cache->h) {
        return (__int128_t)(h_new - cache->h);
    } else {
        return -(__int128_t)(cache->h - h_new);
    }
}

/* --------------------------------------------------------------------------
 * Get all 2n neighbor indices at once (more efficient than 2n separate calls)
 *
 * neighbors[2*i + 0] = index of p - e_i (or -1 if out of bounds)
 * neighbors[2*i + 1] = index of p + e_i (or -1 if out of bounds)
 * -------------------------------------------------------------------------- */

void hilbert_all_neighbors(const hilbert_neighbor_cache_t *cache,
                           hindex_t *neighbors) {
    int n = cache->n;

    for (int axis = 0; axis < n; axis++) {
        neighbors[2 * axis + 0] = hilbert_neighbor_index(cache, axis, -1);
        neighbors[2 * axis + 1] = hilbert_neighbor_index(cache, axis, +1);
    }
}

/* --------------------------------------------------------------------------
 * Analysis: How much work do we save?
 *
 * Full encode: process all mmax levels
 * Neighbor encode: process only (s_top) levels, reuse (mmax - s_top) levels
 *
 * The savings depend on where the highest changed bit is:
 * - Best case (LSB only changes): s_top = 1, save (mmax - 1) levels
 * - Worst case (carry through all bits): s_top = m[axis], save (mmax - m[axis]) levels
 *
 * For uniform random coordinates:
 * - P(s_top = s) depends on trailing zeros/ones in the coordinate
 * - Average s_top ≈ 2 for random incrementsAbs
 * -------------------------------------------------------------------------- */

/* --------------------------------------------------------------------------
 * Test
 * -------------------------------------------------------------------------- */

#ifdef TEST_NEIGHBOR

#include <stdio.h>
#include <stdlib.h>

/* Reference encode from anisotropic_hilbert.c */
extern hindex_t hilbert_encode(const coord_t *point, const int *m, int n);

int main() {
    int m[] = {3, 3, 2};  /* 8 × 8 × 4 */
    int n = 3;

    printf("Testing neighbor index computation on 8×8×4 box\n");
    printf("================================================\n\n");

    hilbert_neighbor_cache_t cache;
    int errors = 0;
    int total_tests = 0;

    /* Test all points and all neighbors */
    uint64_t max_h = (1ULL << (m[0] + m[1] + m[2])) - 1;

    for (uint64_t h = 0; h <= max_h; h++) {
        hilbert_neighbor_init(&cache, h, m, n);

        /* Test each of 2n neighbors */
        for (int axis = 0; axis < n; axis++) {
            for (int delta = -1; delta <= 1; delta += 2) {
                total_tests++;

                /* Compute neighbor index using our function */
                hindex_t h_neighbor = hilbert_neighbor_index(&cache, axis, delta);

                /* Compute reference by explicit encode */
                coord_t neighbor_point[3];
                memcpy(neighbor_point, cache.point, sizeof(neighbor_point));

                bool valid = true;
                if (delta > 0) {
                    if (neighbor_point[axis] >= (1U << m[axis]) - 1) valid = false;
                    else neighbor_point[axis]++;
                } else {
                    if (neighbor_point[axis] == 0) valid = false;
                    else neighbor_point[axis]--;
                }

                hindex_t h_ref = valid ? hilbert_encode(neighbor_point, m, n) : (hindex_t)-1;

                if (h_neighbor != h_ref) {
                    printf("ERROR at h=%llu, axis=%d, delta=%+d\n",
                           (unsigned long long)h, axis, delta);
                    printf("  point=(%u,%u,%u)\n",
                           cache.point[0], cache.point[1], cache.point[2]);
                    printf("  got h_neighbor=%llu, expected=%llu\n",
                           (unsigned long long)h_neighbor, (unsigned long long)h_ref);
                    errors++;
                }
            }
        }
    }

    printf("Tested %d neighbor computations\n", total_tests);
    printf("Errors: %d\n\n", errors);

    /* Show some examples with index deltas */
    printf("Example index deltas (how far apart are neighbors on the curve?):\n");
    printf("------------------------------------------------------------------\n");

    for (uint64_t h = 0; h <= 15 && h <= max_h; h++) {
        hilbert_neighbor_init(&cache, h, m, n);

        printf("h=%2llu p=(%u,%u,%u): ", (unsigned long long)h,
               cache.point[0], cache.point[1], cache.point[2]);

        for (int axis = 0; axis < n; axis++) {
            for (int delta = -1; delta <= 1; delta += 2) {
                __int128_t d = hilbert_neighbor_delta(&cache, axis, delta);
                hindex_t hn = hilbert_neighbor_index(&cache, axis, delta);
                if (hn != (hindex_t)-1) {
                    printf("[%c%c%+4lld] ",
                           "xyz"[axis], delta > 0 ? '+' : '-',
                           (long long)d);
                }
            }
        }
        printf("\n");
    }

    /* Statistics on index deltas */
    printf("\nIndex delta statistics:\n");
    printf("-----------------------\n");

    long long min_delta = 0, max_delta = 0;
    long long sum_abs_delta = 0;
    int delta_count = 0;

    for (uint64_t h = 0; h <= max_h; h++) {
        hilbert_neighbor_init(&cache, h, m, n);

        for (int axis = 0; axis < n; axis++) {
            for (int delta = -1; delta <= 1; delta += 2) {
                __int128_t d = hilbert_neighbor_delta(&cache, axis, delta);
                if (hilbert_neighbor_index(&cache, axis, delta) != (hindex_t)-1) {
                    long long dd = (long long)d;
                    if (dd < min_delta) min_delta = dd;
                    if (dd > max_delta) max_delta = dd;
                    sum_abs_delta += (dd < 0) ? -dd : dd;
                    delta_count++;
                }
            }
        }
    }

    printf("  Min delta: %lld\n", min_delta);
    printf("  Max delta: %lld\n", max_delta);
    printf("  Mean |delta|: %.2f\n", (double)sum_abs_delta / delta_count);
    printf("  (For reference, index range is 0 to %llu)\n", (unsigned long long)max_h);

    /* Count how often |delta| = 1 (neighbor is adjacent on curve) */
    int adj_count = 0;
    for (uint64_t h = 0; h <= max_h; h++) {
        hilbert_neighbor_init(&cache, h, m, n);
        for (int axis = 0; axis < n; axis++) {
            for (int delta = -1; delta <= 1; delta += 2) {
                __int128_t d = hilbert_neighbor_delta(&cache, axis, delta);
                if (hilbert_neighbor_index(&cache, axis, delta) != (hindex_t)-1) {
                    if (d == 1 || d == -1) adj_count++;
                }
            }
        }
    }

    printf("\n  Neighbors that are curve-adjacent (|Δh|=1): %d / %d = %.1f%%\n",
           adj_count, delta_count, 100.0 * adj_count / delta_count);

    return errors;
}

#endif /* TEST_NEIGHBOR */
