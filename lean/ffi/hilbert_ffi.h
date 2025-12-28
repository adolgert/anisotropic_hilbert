/*
 * hilbert_ffi.h
 *
 * C interface to the Lean anisotropic Hilbert curve implementation.
 * This wraps the Lean-exported functions from AnisoHilbert.CExport.
 */

#ifndef HILBERT_FFI_H
#define HILBERT_FFI_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Initialize the Lean runtime. Must be called before any other functions.
 * Returns 0 on success, non-zero on failure.
 */
int hilbert_lean_init(void);

/*
 * Finalize the Lean runtime. Call when done with all Lean operations.
 */
void hilbert_lean_finalize(void);

/*
 * Encode a point to a Hilbert index.
 *
 * @param n_dims     Number of dimensions
 * @param coords     Array of n_dims coordinates
 * @param exponents  Array of n_dims exponents (m_j values, so axis j has 2^m_j points)
 * @return           The Hilbert index (0 on error)
 */
uint64_t hilbert_lean_encode(uint32_t n_dims, const uint32_t *coords, const uint32_t *exponents);

/*
 * Decode a Hilbert index to a point.
 *
 * @param n_dims     Number of dimensions
 * @param exponents  Array of n_dims exponents
 * @param index      The Hilbert index to decode
 * @param coords_out Output array of n_dims coordinates (must be pre-allocated)
 */
void hilbert_lean_decode(uint32_t n_dims, const uint32_t *exponents, uint64_t index, uint32_t *coords_out);

#ifdef __cplusplus
}
#endif

#endif /* HILBERT_FFI_H */
