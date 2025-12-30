/*
 * hamilton.c
 *
 * Hamilton's Compact Hilbert Index algorithm (2008) for domains with unequal side lengths.
 *
 * This is a faithful C translation of Algorithm 4 from:
 *   Hamilton & Rau-Chaplin, "Compact Hilbert indices: Space-filling curves for
 *   domains with unequal side lengths", Information Processing Letters 105 (2008) 155-163.
 *
 * WARNING: This implementation contains the bug present in the original paper.
 * The direction parameter `d` is NOT reindexed when the active axis set changes.
 * This causes discontinuities in the resulting curve for certain anisotropic boxes.
 */

#include "hamilton.h"
#include <stdbool.h>
#include <string.h>
#include <assert.h>

/* ========================================================================== */
/* Bit manipulation helpers                                                   */
/* ========================================================================== */

static inline uint32_t mask_bits(uint32_t bits)
{
    return (bits >= 32u) ? 0xFFFFFFFFu : ((1u << bits) - 1u);
}

static inline uint32_t rotr_bits(uint32_t x, uint32_t r, uint32_t bits)
{
    if (bits == 0u)
        return x;
    if (bits == 32u)
    {
        r &= 31u;
        return (r == 0u) ? x : (uint32_t)((x >> r) | (x << (32u - r)));
    }
    const uint32_t mask = mask_bits(bits);
    x &= mask;
    r %= bits;
    if (r == 0u)
        return x;
    return (uint32_t)(((x >> r) | (x << (bits - r))) & mask);
}

static inline uint32_t rotl_bits(uint32_t x, uint32_t r, uint32_t bits)
{
    if (bits == 0u)
        return x;
    if (bits == 32u)
    {
        r &= 31u;
        return (r == 0u) ? x : (uint32_t)((x << r) | (x >> (32u - r)));
    }
    const uint32_t mask = mask_bits(bits);
    x &= mask;
    r %= bits;
    if (r == 0u)
        return x;
    return (uint32_t)(((x << r) | (x >> (bits - r))) & mask);
}

/* ========================================================================== */
/* Hamilton's Gray code functions                                             */
/* ========================================================================== */

/* Binary reflected Gray code: gc(i) = i XOR (i >> 1) */
static inline uint32_t gray_code(uint32_t i)
{
    return i ^ (i >> 1);
}

/* Inverse of binary reflected Gray code */
static inline uint32_t gray_decode(uint32_t g)
{
    uint32_t i = 0;
    while (g)
    {
        i ^= g;
        g >>= 1;
    }
    return i;
}

/* Number of trailing 1-bits (Hamilton's tsb function) */
static inline uint32_t trailing_ones(uint32_t i)
{
    uint32_t c = 0;
    while (i & 1u)
    {
        c++;
        i >>= 1;
    }
    return c;
}

/* ========================================================================== */
/* Hamilton's T-transform                                                     */
/* ========================================================================== */

/*
 * Hamilton T-transform:
 *   T(e,d)(b) = (b XOR e) rotated-right by (d+1) (mod bits)
 */
static inline uint32_t T_transform(uint32_t e, uint32_t d, uint32_t bits, uint32_t b)
{
    if (bits == 0u)
        return 0u;
    return rotr_bits((b ^ e) & mask_bits(bits), (d + 1u) % bits, bits);
}

/*
 * Inverse of T(e,d). Since T is (XOR e) then rotate-right, the inverse is:
 *   rotate-left by (d+1), then XOR e.
 */
static inline uint32_t T_transform_inv(uint32_t e, uint32_t d, uint32_t bits, uint32_t b)
{
    if (bits == 0u)
        return 0u;
    return (rotl_bits(b & mask_bits(bits), (d + 1u) % bits, bits) ^ e) & mask_bits(bits);
}

/* ========================================================================== */
/* Hamilton's entry and direction sequences                                   */
/* ========================================================================== */

/*
 * Hamilton entry-point sequence e(i) for a k=bits dimensional cube.
 * Theorem 2.10: e(0)=0; e(i)=gc(2*floor((i-1)/2)) for i>0.
 */
static inline uint32_t e_seq(uint32_t bits, uint32_t i)
{
    (void)bits; /* unused, but kept for API consistency */
    if (i == 0)
        return 0;
    return gray_code(2u * ((i - 1u) / 2u));
}

/*
 * Hamilton intra-subcube direction sequence d(i) for k=bits dimensions.
 * Theorem 2.9 / Lemma 2.8:
 *   d(0)=0
 *   d(i)=g(i-1) if i even
 *   d(i)=g(i)   if i odd
 * where g(i) = trailing_ones(i) and all indices are reduced mod bits.
 */
static inline uint32_t d_seq(uint32_t bits, uint32_t i)
{
    if (bits == 0u)
        return 0u;
    if (i == 0)
        return 0;
    if (i & 1u)
        return trailing_ones(i) % bits;
    return trailing_ones(i - 1u) % bits;
}

/* ========================================================================== */
/* Axis ordering by priority                                                  */
/* ========================================================================== */

typedef struct
{
    int axis;
    int exp;
} axis_exp_t;

/* Sort axes by priority (m_j, j) - smaller exponent first, then by axis id */
static void sort_axes_by_priority(const int *m, int n, int *order)
{
    axis_exp_t items[HAMILTON_MAX_DIMS];
    for (int i = 0; i < n; i++)
    {
        items[i].axis = i;
        items[i].exp = m[i];
    }
    /* Insertion sort (stable, good for small n) */
    for (int i = 1; i < n; i++)
    {
        axis_exp_t key = items[i];
        int j = i - 1;
        while (j >= 0 && (items[j].exp > key.exp ||
                          (items[j].exp == key.exp && items[j].axis > key.axis)))
        {
            items[j + 1] = items[j];
            j--;
        }
        items[j + 1] = key;
    }
    for (int i = 0; i < n; i++)
    {
        order[i] = items[i].axis;
    }
}

/* ========================================================================== */
/* Curve structure                                                            */
/* ========================================================================== */

typedef struct
{
    int mmax;                              /* max(exponent bits) */
    int total_bits;                        /* sum(exponent bits) */
    int k_level[HAMILTON_MAX_LEVELS + 1];  /* Number of active axes at level s */
    int axes_ordered[HAMILTON_MAX_DIMS];   /* Axes sorted by priority */
} hamilton_curve_t;

static bool build_curve(const int *m, int n, hamilton_curve_t *curve)
{
    if (!m || n <= 0 || n > HAMILTON_MAX_DIMS || !curve)
        return false;

    int mmax = 0;
    int total_bits = 0;
    for (int i = 0; i < n; i++)
    {
        if (m[i] < 0 || m[i] > HAMILTON_MAX_LEVELS)
            return false;
        if (m[i] > mmax)
            mmax = m[i];
        total_bits += m[i];
    }
    if (total_bits > HAMILTON_MAX_INDEX_BITS)
        return false;

    curve->mmax = mmax;
    curve->total_bits = total_bits;

    sort_axes_by_priority(m, n, curve->axes_ordered);
    curve->k_level[0] = 0;

    /* Compute k(s) = number of active axes at level s */
    int axis_idx = 0;
    for (int s = 1; s <= mmax; s++)
    {
        while (axis_idx < n && m[curve->axes_ordered[axis_idx]] < s)
        {
            axis_idx++;
        }
        curve->k_level[s] = n - axis_idx;
    }

    return true;
}

/* ========================================================================== */
/* Gather/scatter bits                                                        */
/* ========================================================================== */

/*
 * Gather bits from coordinates into a plane value.
 * Collects bit (s-1) from each active axis into a k-bit plane.
 */
static inline uint32_t gather_plane(const hamilton_coord_t *point, const int *A, int k, int s)
{
    uint32_t plane = 0u;
    for (int j = 0; j < k; j++)
    {
        int ax = A[j];
        plane |= ((point[ax] >> (s - 1)) & 1u) << j;
    }
    return plane;
}

/*
 * Scatter bits from a plane value to coordinates.
 * Distributes each bit of the k-bit plane to bit (s-1) of the corresponding axis.
 */
static inline void scatter_plane(hamilton_coord_t *point, const int *A, int k, int s, uint32_t plane)
{
    for (int j = 0; j < k; j++)
    {
        int ax = A[j];
        point[ax] |= ((plane >> j) & 1u) << (s - 1);
    }
}

/* ========================================================================== */
/* Public API                                                                 */
/* ========================================================================== */

hamilton_index_t hamilton_encode(const hamilton_coord_t *point, const int *m, int n)
{
    hamilton_curve_t curve;
    memset(&curve, 0, sizeof(curve));

    if (!point || !m)
        return (hamilton_index_t)0;
    if (!build_curve(m, n, &curve))
        return (hamilton_index_t)0;
    if (curve.mmax == 0)
        return (hamilton_index_t)0;

    hamilton_index_t h = 0;
    uint32_t e = 0;
    uint32_t d = 0;

    for (int s = curve.mmax; s >= 1; s--)
    {
        int k = curve.k_level[s];
        assert(k != 0);

        uint32_t mask = mask_bits((uint32_t)k);

        /*
         * BUG (from original paper): We mask e and d to k bits, but when k grows,
         * we don't properly reindex d to refer to the same physical axis.
         */
        e &= mask;
        d %= (uint32_t)k;

        /* Get active axes for this level */
        int first_axis = n - k;
        const int *A = curve.axes_ordered + first_axis;

        /* Pack the (s-1) bit across active axes into an integer l (k bits) */
        uint32_t l = gather_plane(point, A, k, s);

        /* Hamilton step: transform to standard orientation, Gray-decode to get w */
        uint32_t l_t = T_transform(e, d, (uint32_t)k, l);
        uint32_t w = gray_decode(l_t);

        /* Append this variable-width digit */
        h = (h << k) | (hamilton_index_t)w;

        /* Update orientation using the cube's e(w), d(w) */
        e = e ^ rotl_bits(e_seq((uint32_t)k, w), (d + 1u) % (uint32_t)k, (uint32_t)k);
        d = (d + d_seq((uint32_t)k, w) + 1u) % (uint32_t)k;

        /*
         * BUG: NO activation embedding here!
         * When the active set grows (k_{s-1} > k_s), Hamilton's algorithm
         * does NOT reindex d to preserve the physical axis it refers to.
         * This causes discontinuities at activation boundaries.
         */
    }

    return h;
}

void hamilton_decode(hamilton_index_t h, const int *m, int n, hamilton_coord_t *point)
{
    if (!point || !m || n <= 0 || n > HAMILTON_MAX_DIMS)
        return;
    memset(point, 0, (size_t)n * sizeof(hamilton_coord_t));

    hamilton_curve_t curve;
    memset(&curve, 0, sizeof(curve));

    if (!build_curve(m, n, &curve))
        return;
    if (curve.mmax == 0)
        return;

    int bit_pos = curve.total_bits;
    uint32_t e = 0;
    uint32_t d = 0;

    for (int s = curve.mmax; s >= 1; s--)
    {
        int k = curve.k_level[s];
        assert(k != 0);

        uint32_t mask = mask_bits((uint32_t)k);

        /*
         * BUG (from original paper): We mask e and d to k bits, but when k grows,
         * we don't properly reindex d to refer to the same physical axis.
         */
        e &= mask;
        d %= (uint32_t)k;

        /* Get active axes for this level */
        int first_axis = n - k;
        const int *A = curve.axes_ordered + first_axis;

        /* Extract the variable-width digit w */
        bit_pos -= k;
        uint32_t w = (uint32_t)((h >> bit_pos) & (hamilton_index_t)mask);

        /* Hamilton inverse step: Gray-encode w, untransform back to current orientation */
        uint32_t g = gray_code(w);
        uint32_t l = T_transform_inv(e, d, (uint32_t)k, g);

        /* Write the recovered bit into each active axis coordinate */
        scatter_plane(point, A, k, s, l);

        /* Update orientation (same as encode) */
        e = e ^ rotl_bits(e_seq((uint32_t)k, w), (d + 1u) % (uint32_t)k, (uint32_t)k);
        d = (d + d_seq((uint32_t)k, w) + 1u) % (uint32_t)k;

        /* BUG: NO activation embedding here! */
    }
}

uint64_t hamilton_encode_64(const hamilton_coord_t *point, const int *m, int n)
{
    return (uint64_t)hamilton_encode(point, m, n);
}

void hamilton_decode_64(uint64_t h, const int *m, int n, hamilton_coord_t *point)
{
    hamilton_decode((hamilton_index_t)h, m, n, point);
}

void hamilton_encode_128(const hamilton_coord_t *point, const int *m, int n,
                         uint64_t *h_lo, uint64_t *h_hi)
{
    hamilton_index_t h = hamilton_encode(point, m, n);
    *h_lo = (uint64_t)h;
    *h_hi = (uint64_t)(h >> 64);
}

void hamilton_decode_128(uint64_t h_lo, uint64_t h_hi, const int *m, int n,
                         hamilton_coord_t *point)
{
    hamilton_index_t h = ((hamilton_index_t)h_hi << 64) | h_lo;
    hamilton_decode(h, m, n, point);
}
