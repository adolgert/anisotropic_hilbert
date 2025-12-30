/*
 * setup_hilbert.h
 *
 * Global context for HDF5-based Hilbert curve table lookups.
 * Provides the same function signatures as random_tables.h but loads
 * tables from HDF5 files at runtime.
 *
 * Usage:
 *   1. Call hilbert_tables_init() once at program start
 *   2. Use hilbert_gray(), hilbert_gray_rank(), etc. as before
 *   3. Call hilbert_tables_switch() to change table sets
 *   4. Call hilbert_tables_cleanup() at program end
 */

#ifndef SETUP_HILBERT_H
#define SETUP_HILBERT_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Initialize global Hilbert tables from HDF5 file.
 * Must be called before any hilbert_gray/etc functions.
 *
 * filename: Path to HDF5 file containing Hilbert tables
 * name: Table family name ("brgc", "monotone", "balanced", "random")
 * index: Index within that family (0, 1, 2, ...)
 *
 * Returns 0 on success, -1 on error.
 */
int hilbert_tables_init(const char* filename, const char* name, int index);

/*
 * Cleanup global Hilbert tables context.
 * Safe to call multiple times or with no prior init.
 */
void hilbert_tables_cleanup(void);

/*
 * Change to a different table set (same file).
 * Requires hilbert_tables_init() to have been called first.
 *
 * Returns 0 on success, -1 on error.
 */
int hilbert_tables_switch(const char* name, int index);

/*
 * Table lookup functions - same signatures as random_tables.h
 *
 * k: dimension (1..8)
 * w: position index (0..2^k-1)
 * g: Gray code value (0..2^k-1)
 *
 * Returns 0 on error (no tables loaded, k out of range, etc.)
 */
uint8_t hilbert_gray(uint32_t k, uint32_t w);
uint8_t hilbert_gray_rank(uint32_t k, uint32_t g);
uint8_t hilbert_child_entry(uint32_t k, uint32_t w);
uint8_t hilbert_child_dir(uint32_t k, uint32_t w);

#ifdef __cplusplus
}
#endif

#endif /* SETUP_HILBERT_H */
