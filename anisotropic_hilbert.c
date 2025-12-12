/*
 * anisotropic_hilbert.c
 *
 * A continuous (lattice-continuous) Hilbert-like space-filling curve on an
 * axis-aligned dyadic box 2^{m0} × ... × 2^{m_{n-1}}.
 *
 * This implementation follows the geometric machinery in:
 *   Chris Hamilton, "Compact Hilbert Indices", Technical Report CS-2006-07 (2006)
 *
 * Supports up to MAX_DIMS dimensions and uses __uint128_t for Hilbert indices
 * to handle large sum(m) values.
 */

#include <stdint.h>
#include <string.h>
#include <stdbool.h>

#define MAX_DIMS 32

/* Use 128-bit integers for Hilbert indices (GCC/Clang extension) */
typedef __uint128_t hindex_t;
typedef uint32_t coord_t;

/* --------------------------------------------------------------------------
 * Bit manipulation primitives
 * -------------------------------------------------------------------------- */

static inline uint32_t gray_code(uint32_t i) {
    return i ^ (i >> 1);
}

static inline uint32_t gray_decode(uint32_t g) {
    uint32_t i = 0;
    while (g) {
        i ^= g;
        g >>= 1;
    }
    return i;
}

static inline int trailing_ones(uint32_t i) {
    int c = 0;
    while (i & 1) {
        c++;
        i >>= 1;
    }
    return c;
}

static inline uint32_t mask_bits(int bits) {
    return bits > 0 ? ((1U << bits) - 1) : 0;
}

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

/* Hamilton T-transform: T(e,d)(b) = (b XOR e) rotated-right by (d+1) */
static inline uint32_t T_transform(uint32_t e, int d, int bits, uint32_t b) {
    return rrotate((b ^ e) & mask_bits(bits), (d + 1) % bits, bits);
}

/* Inverse of T(e,d) */
static inline uint32_t T_inv(uint32_t e, int d, int bits, uint32_t b) {
    return (lrotate(b & mask_bits(bits), (d + 1) % bits, bits) ^ e) & mask_bits(bits);
}

/* Entry-point sequence e(i) */
static inline uint32_t e_seq(int i) {
    if (i == 0) return 0;
    return gray_code(2 * ((i - 1) / 2));
}

/* Direction sequence d(i) */
static inline int d_seq(int bits, int i) {
    if (i == 0) return 0;
    if (i & 1) return trailing_ones(i) % bits;
    return trailing_ones(i - 1) % bits;
}

/* --------------------------------------------------------------------------
 * Axis ordering and active axes
 * -------------------------------------------------------------------------- */

/* Comparison function for sorting axes by (m[ax], ax) */
typedef struct {
    int axis;
    int exp;
} axis_exp_t;

static void sort_axes_by_exp(const int *m, int n, int *order) {
    axis_exp_t items[MAX_DIMS];
    for (int i = 0; i < n; i++) {
        items[i].axis = i;
        items[i].exp = m[i];
    }
    /* Simple insertion sort (n is small) */
    for (int i = 1; i < n; i++) {
        axis_exp_t key = items[i];
        int j = i - 1;
        while (j >= 0 && (items[j].exp > key.exp ||
               (items[j].exp == key.exp && items[j].axis > key.axis))) {
            items[j + 1] = items[j];
            j--;
        }
        items[j + 1] = key;
    }
    for (int i = 0; i < n; i++) {
        order[i] = items[i].axis;
    }
}

/* Get active axes at level s, returns count */
static int get_active_axes(const int *m, int n, int s, const int *order, int *active) {
    int k = 0;
    for (int i = 0; i < n; i++) {
        int ax = order[i];
        if (m[ax] >= s) {
            active[k++] = ax;
        }
    }
    return k;
}

/* Embed state from smaller to larger active set */
static void embed_state(const int *A_old, int k_old, const int *A_new, int k_new,
                        uint32_t e_old, int d_old, uint32_t *e_new, int *d_new) {
    /* Build position map for new axes */
    int pos_new[MAX_DIMS];
    for (int j = 0; j < k_new; j++) {
        pos_new[A_new[j]] = j;
    }

    /* Copy e bits to new positions */
    *e_new = 0;
    for (int j = 0; j < k_old; j++) {
        if ((e_old >> j) & 1) {
            *e_new |= 1U << pos_new[A_old[j]];
        }
    }

    /* Reindex d by axis label */
    int dir_axis = A_old[d_old];
    *d_new = pos_new[dir_axis];
}

/* --------------------------------------------------------------------------
 * Main encode/decode functions
 * -------------------------------------------------------------------------- */

/*
 * Encode a point to its Hilbert index.
 *
 * Parameters:
 *   point: array of n coordinates
 *   m: array of n exponents (box is 2^m[0] x ... x 2^m[n-1])
 *   n: number of dimensions
 *
 * Returns: Hilbert index
 */
hindex_t hilbert_encode(const coord_t *restrict point, const int *restrict m, int n) {
    if (n <= 0 || n > MAX_DIMS) return 0;

    int mmax = 0;
    for (int i = 0; i < n; i++) {
        if (m[i] > mmax) mmax = m[i];
    }
    if (mmax == 0) return 0;

    /* Precompute axis order */
    int order[MAX_DIMS];
    sort_axes_by_exp(m, n, order);

    /* Precompute active axes for each level */
    int active[MAX_DIMS][MAX_DIMS];
    int k_at_level[MAX_DIMS + 1];
    for (int s = 1; s <= mmax; s++) {
        k_at_level[s] = get_active_axes(m, n, s, order, active[s]);
    }

    hindex_t h = 0;
    uint32_t e = 0;
    int d = 0;

    for (int s = mmax; s >= 1; s--) {
        int *A = active[s];
        int k = k_at_level[s];

        e &= mask_bits(k);
        d = d % k;

        /* Pack the (s-1) bit across active axes */
        uint32_t l = 0;
        for (int j = 0; j < k; j++) {
            int ax = A[j];
            l |= ((point[ax] >> (s - 1)) & 1) << j;
        }

        /* Hamilton step */
        uint32_t l_t = T_transform(e, d, k, l);
        uint32_t w = gray_decode(l_t);

        /* Append digit */
        h = (h << k) | w;

        /* Update orientation */
        e = e ^ lrotate(e_seq(w), (d + 1) % k, k);
        d = (d + d_seq(k, w) + 1) % k;

        /* Embed if active set grows */
        if (s > 1 && k_at_level[s - 1] > k) {
            uint32_t e_new;
            int d_new;
            embed_state(A, k, active[s - 1], k_at_level[s - 1], e, d, &e_new, &d_new);
            e = e_new;
            d = d_new;
        }
    }

    return h;
}

/*
 * Decode a Hilbert index to its point.
 *
 * Parameters:
 *   h: Hilbert index
 *   m: array of n exponents
 *   n: number of dimensions
 *   point: output array of n coordinates
 */
void hilbert_decode(hindex_t h, const int *restrict m, int n, coord_t *restrict point) {
    memset(point, 0, n * sizeof(coord_t));

    if (n <= 0 || n > MAX_DIMS) return;

    int mmax = 0;
    int total_bits = 0;
    for (int i = 0; i < n; i++) {
        if (m[i] > mmax) mmax = m[i];
        total_bits += m[i];
    }
    if (mmax == 0) return;

    /* Precompute axis order */
    int order[MAX_DIMS];
    sort_axes_by_exp(m, n, order);

    /* Precompute active axes for each level */
    int active[MAX_DIMS][MAX_DIMS];
    int k_at_level[MAX_DIMS + 1];
    for (int s = 1; s <= mmax; s++) {
        k_at_level[s] = get_active_axes(m, n, s, order, active[s]);
    }

    /* Compute segment sizes and bit position */
    int bit_pos = total_bits;

    uint32_t e = 0;
    int d = 0;

    for (int s = mmax; s >= 1; s--) {
        int *A = active[s];
        int k = k_at_level[s];

        bit_pos -= k;
        uint32_t w = (uint32_t)((h >> bit_pos) & mask_bits(k));

        /* Hamilton inverse step */
        uint32_t l = gray_code(w);
        l = T_inv(e, d, k, l);

        /* Write recovered bits */
        for (int j = 0; j < k; j++) {
            int ax = A[j];
            point[ax] |= ((l >> j) & 1) << (s - 1);
        }

        /* Update orientation */
        e = e ^ lrotate(e_seq(w), (d + 1) % k, k);
        d = (d + d_seq(k, w) + 1) % k;

        /* Embed if active set grows */
        if (s > 1 && k_at_level[s - 1] > k) {
            uint32_t e_new;
            int d_new;
            embed_state(A, k, active[s - 1], k_at_level[s - 1], e, d, &e_new, &d_new);
            e = e_new;
            d = d_new;
        }
    }
}

/* --------------------------------------------------------------------------
 * Batch operations for efficiency
 * -------------------------------------------------------------------------- */

/*
 * Decode multiple consecutive Hilbert indices starting from h_start.
 * Writes n_points * n coordinates to points array (row-major).
 */
void hilbert_decode_batch(hindex_t h_start, uint64_t n_points,
                          const int *restrict m, int n,
                          coord_t *restrict points) {
    for (uint64_t i = 0; i < n_points; i++) {
        hilbert_decode(h_start + i, m, n, points + i * n);
    }
}

/*
 * Encode multiple points.
 * points is row-major array of n_points * n coordinates.
 * indices is output array of n_points Hilbert indices.
 */
void hilbert_encode_batch(const coord_t *restrict points, uint64_t n_points,
                          const int *restrict m, int n,
                          hindex_t *restrict indices) {
    for (uint64_t i = 0; i < n_points; i++) {
        indices[i] = hilbert_encode(points + i * n, m, n);
    }
}

/* --------------------------------------------------------------------------
 * C-compatible wrapper functions for ctypes (64-bit index versions)
 *
 * Since ctypes doesn't directly support __uint128_t, we provide 64-bit
 * versions that work for sum(m) <= 64. For larger indices, use the
 * hi/lo split versions.
 * -------------------------------------------------------------------------- */

uint64_t hilbert_encode_64(const coord_t *point, const int *m, int n) {
    return (uint64_t)hilbert_encode(point, m, n);
}

void hilbert_decode_64(uint64_t h, const int *m, int n, coord_t *point) {
    hilbert_decode((hindex_t)h, m, n, point);
}

/* 128-bit versions using hi/lo split */
void hilbert_encode_128(const coord_t *point, const int *m, int n,
                        uint64_t *h_lo, uint64_t *h_hi) {
    hindex_t h = hilbert_encode(point, m, n);
    *h_lo = (uint64_t)h;
    *h_hi = (uint64_t)(h >> 64);
}

void hilbert_decode_128(uint64_t h_lo, uint64_t h_hi, const int *m, int n,
                        coord_t *point) {
    hindex_t h = ((hindex_t)h_hi << 64) | h_lo;
    hilbert_decode(h, m, n, point);
}

/* Batch versions (64-bit) */
void hilbert_decode_batch_64(uint64_t h_start, uint64_t n_points,
                             const int *m, int n, coord_t *points) {
    hilbert_decode_batch((hindex_t)h_start, n_points, m, n, points);
}

void hilbert_encode_batch_64(const coord_t *points, uint64_t n_points,
                             const int *m, int n, uint64_t *indices) {
    for (uint64_t i = 0; i < n_points; i++) {
        indices[i] = (uint64_t)hilbert_encode(points + i * n, m, n);
    }
}

/* Utility: compute total index bits */
int hilbert_index_bits(const int *m, int n) {
    int total = 0;
    for (int i = 0; i < n; i++) {
        total += m[i];
    }
    return total;
}
