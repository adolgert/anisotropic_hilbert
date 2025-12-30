/*
 * hamilton.h
 *
 * Hamilton's Compact Hilbert Index algorithm (2008) for domains with unequal side lengths.
 *
 * This is a faithful implementation of Algorithm 4 from:
 *   Hamilton & Rau-Chaplin, "Compact Hilbert indices: Space-filling curves for
 *   domains with unequal side lengths", Information Processing Letters 105 (2008) 155-163.
 *
 * WARNING: This implementation contains the bug present in the original paper.
 * The direction parameter `d` is NOT reindexed when the active axis set changes.
 * This causes discontinuities in the resulting curve for certain anisotropic boxes.
 *
 * Use hilbert_affine_encode/decode for a corrected implementation that guarantees
 * lattice continuity.
 *
 * This file exists to demonstrate the bug and provide a baseline for comparison
 * in metrics calculations.
 */

#ifndef HAMILTON_H
#define HAMILTON_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define HAMILTON_MAX_DIMS 32
#define HAMILTON_MAX_LEVELS 32
#define HAMILTON_MAX_INDEX_BITS 128

typedef __uint128_t hamilton_index_t;
typedef uint32_t hamilton_coord_t;

/*
 * Encode a point to its Hamilton Compact Hilbert index.
 *
 * Parameters:
 *   point - array of n coordinates, each in [0, 2^m[i])
 *   m     - array of n exponents (bits per axis)
 *   n     - number of dimensions
 *
 * Returns:
 *   Hilbert index in [0, 2^{sum(m)})
 */
hamilton_index_t hamilton_encode(const hamilton_coord_t *point, const int *m, int n);

/*
 * Decode a Hamilton Compact Hilbert index to its point.
 *
 * Parameters:
 *   h     - Hilbert index in [0, 2^{sum(m)})
 *   m     - array of n exponents (bits per axis)
 *   n     - number of dimensions
 *   point - output array of n coordinates
 */
void hamilton_decode(hamilton_index_t h, const int *m, int n, hamilton_coord_t *point);

/*
 * 64-bit convenience wrappers (for indices fitting in 64 bits)
 */
uint64_t hamilton_encode_64(const hamilton_coord_t *point, const int *m, int n);
void hamilton_decode_64(uint64_t h, const int *m, int n, hamilton_coord_t *point);

/*
 * 128-bit explicit wrappers (for FFI compatibility)
 */
void hamilton_encode_128(const hamilton_coord_t *point, const int *m, int n,
                         uint64_t *h_lo, uint64_t *h_hi);
void hamilton_decode_128(uint64_t h_lo, uint64_t h_hi, const int *m, int n,
                         hamilton_coord_t *point);

#ifdef __cplusplus
}
#endif

#endif /* HAMILTON_H */
