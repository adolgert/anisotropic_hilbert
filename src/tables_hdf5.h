/*
 * tables_hdf5.h
 *
 * HDF5-based storage and retrieval for Hilbert curve tables.
 *
 * This module provides a context-based API for storing and loading
 * Hilbert curve lookup tables (Gray code, Gray rank, child entry,
 * child direction) from HDF5 files.
 *
 * Tables are organized by:
 *   - name: "random", "brgc", "balanced", "monotone"
 *   - index: integer index within that name (0, 1, 2, ...)
 *   - k: dimension (1..8)
 *
 * HDF5 structure:
 *   /<name>/<index>/<k>/gray        [2^k x uint8]
 *   /<name>/<index>/<k>/gray_rank   [2^k x uint8]
 *   /<name>/<index>/<k>/child_entry [2^k x uint8]
 *   /<name>/<index>/<k>/child_dir   [2^k x uint8]
 */

#ifndef TABLES_HDF5_H
#define TABLES_HDF5_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Opaque context type */
typedef struct hilbert_tables_ctx hilbert_tables_ctx_t;

/* --------------------------------------------------------------------------
 * Context Management
 * -------------------------------------------------------------------------- */

/*
 * Open an existing HDF5 file for reading tables.
 * Returns NULL on error.
 */
hilbert_tables_ctx_t* hilbert_tables_open(const char* filename);

/*
 * Create a new HDF5 file (or truncate existing) for writing tables.
 * The file is opened in read/write mode.
 * Returns NULL on error.
 */
hilbert_tables_ctx_t* hilbert_tables_create(const char* filename);

/*
 * Open an existing HDF5 file for writing (appending) tables.
 * If the file doesn't exist, creates a new one.
 * Returns NULL on error.
 */
hilbert_tables_ctx_t* hilbert_tables_open_rw(const char* filename);

/*
 * Close the context and free resources.
 * Safe to call with NULL.
 */
void hilbert_tables_close(hilbert_tables_ctx_t* ctx);

/* --------------------------------------------------------------------------
 * Query Available Tables
 * -------------------------------------------------------------------------- */

/*
 * Returns the count of table sets available for the given name.
 * Returns 0 if the name doesn't exist or on error.
 *
 * name: "random", "brgc", "balanced", "monotone", etc.
 */
int hilbert_tables_count(hilbert_tables_ctx_t* ctx, const char* name);

/* --------------------------------------------------------------------------
 * Select Current Table
 * -------------------------------------------------------------------------- */

/*
 * Set the active table by name and index.
 * Subsequent lookup calls will use this table.
 *
 * Returns 0 on success, -1 on error (e.g., name/index doesn't exist).
 */
int hilbert_tables_select(hilbert_tables_ctx_t* ctx, const char* name, int index);

/* --------------------------------------------------------------------------
 * Table Lookup (auto-loads k on demand)
 * -------------------------------------------------------------------------- */

/*
 * Look up values in the currently selected table.
 * These functions auto-load the table for the given k if not already cached.
 *
 * k: dimension (1..8)
 * w: position index (0..2^k-1)
 * g: Gray code value (0..2^k-1)
 *
 * Returns 0 on error (no table selected, k out of range, etc.)
 */
uint8_t hilbert_gray(hilbert_tables_ctx_t* ctx, uint32_t k, uint32_t w);
uint8_t hilbert_gray_rank(hilbert_tables_ctx_t* ctx, uint32_t k, uint32_t g);
uint8_t hilbert_child_entry(hilbert_tables_ctx_t* ctx, uint32_t k, uint32_t w);
uint8_t hilbert_child_dir(hilbert_tables_ctx_t* ctx, uint32_t k, uint32_t w);

/* --------------------------------------------------------------------------
 * Storage API (for table generation)
 * -------------------------------------------------------------------------- */

/*
 * Add or overwrite a table set in the HDF5 file.
 *
 * name:  Table family name ("random", "brgc", etc.)
 * index: Index within that family
 * k:     Dimension (1..8)
 * gray, gray_rank, child_entry, child_dir: Arrays of size 2^k
 *
 * If the table set (name, index, k) already exists, it is replaced.
 *
 * Returns 0 on success, -1 on error.
 */
int hilbert_tables_add(hilbert_tables_ctx_t* ctx,
                       const char* name, int index, int k,
                       const uint8_t* gray,
                       const uint8_t* gray_rank,
                       const uint8_t* child_entry,
                       const uint8_t* child_dir);

#ifdef __cplusplus
}
#endif

#endif /* TABLES_HDF5_H */
