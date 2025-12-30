/*
 * setup_hilbert.c
 *
 * Global context wrapper for HDF5-based Hilbert curve table lookups.
 * Provides context-free function signatures compatible with random_tables.h.
 */

#include "setup_hilbert.h"
#include "tables_hdf5.h"
#include <stdlib.h>

/* Global context - must be initialized before use */
static hilbert_tables_ctx_t* g_ctx = NULL;

int hilbert_tables_init(const char* filename, const char* name, int index)
{
    /* Close any existing context */
    if (g_ctx) {
        hilbert_tables_close(g_ctx);
        g_ctx = NULL;
    }

    /* Open the HDF5 file */
    g_ctx = hilbert_tables_open(filename);
    if (!g_ctx) {
        return -1;
    }

    /* Select the specified table set */
    if (hilbert_tables_select(g_ctx, name, index) < 0) {
        hilbert_tables_close(g_ctx);
        g_ctx = NULL;
        return -1;
    }

    return 0;
}

void hilbert_tables_cleanup(void)
{
    if (g_ctx) {
        hilbert_tables_close(g_ctx);
        g_ctx = NULL;
    }
}

int hilbert_tables_switch(const char* name, int index)
{
    if (!g_ctx) {
        return -1;
    }
    return hilbert_tables_select(g_ctx, name, index);
}

uint8_t hilbert_gray(uint32_t k, uint32_t w)
{
    return hilbert_gray_ctx(g_ctx, k, w);
}

uint8_t hilbert_gray_rank(uint32_t k, uint32_t g)
{
    return hilbert_gray_rank_ctx(g_ctx, k, g);
}

uint8_t hilbert_child_entry(uint32_t k, uint32_t w)
{
    return hilbert_child_entry_ctx(g_ctx, k, w);
}

uint8_t hilbert_child_dir(uint32_t k, uint32_t w)
{
    return hilbert_child_dir_ctx(g_ctx, k, w);
}
