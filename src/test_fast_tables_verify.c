/*
 * test_fast_tables_verify.c
 *
 * Verification program for generate_fast_tables output.
 * Reads an HDF5 file and validates the Hilbert table structure.
 *
 * Usage: test_fast_tables_verify FILE.h5 NAME INDEX
 */

#include "tables_hdf5.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Compute BRGC for verification */
static uint8_t brgc(uint8_t i) { return i ^ (i >> 1); }

/* Count trailing ones in binary representation */
static uint32_t trailing_ones(uint32_t x)
{
    uint32_t c = 0;
    while ((x & 1u) != 0u)
    {
        c++;
        x >>= 1u;
    }
    return c;
}

/* Hamilton's standard child_entry for BRGC */
static uint8_t child_entry_std(uint32_t w)
{
    if (w == 0u)
        return 0u;
    return brgc((uint8_t)((w - 1u) & ~1u));
}

/* Hamilton's standard child_dir for BRGC */
static uint8_t child_dir_std(uint32_t w, uint32_t k)
{
    if (w == 0u)
        return 0u;
    if ((w & 1u) != 0u)
        return (uint8_t)(trailing_ones(w) % k);
    return (uint8_t)(trailing_ones(w - 1u) % k);
}

/* Verify that gray is a valid Gray code: a permutation where consecutive
   elements differ by exactly one bit */
static int verify_gray_code(hilbert_tables_ctx_t *ctx, int k)
{
    uint32_t size = 1u << k;
    uint8_t *seen = calloc(size, 1);
    if (!seen)
        return 0;

    for (uint32_t w = 0; w < size; w++)
    {
        uint8_t g = hilbert_gray(ctx, k, w);
        if (g >= size)
        {
            free(seen);
            return 0;
        }
        if (seen[g])
        {
            free(seen);
            return 0; /* duplicate */
        }
        seen[g] = 1;

        /* Check Gray code property: consecutive elements differ by 1 bit */
        if (w > 0)
        {
            uint8_t prev = hilbert_gray(ctx, k, w - 1);
            uint8_t diff = g ^ prev;
            /* diff should be a power of 2 */
            if (diff == 0 || (diff & (diff - 1)) != 0)
            {
                free(seen);
                return 0;
            }
        }
    }

    free(seen);
    return 1;
}

/* Verify gray_rank is inverse of gray */
static int verify_gray_rank(hilbert_tables_ctx_t *ctx, int k)
{
    uint32_t size = 1u << k;

    for (uint32_t w = 0; w < size; w++)
    {
        uint8_t g = hilbert_gray(ctx, k, w);
        uint8_t r = hilbert_gray_rank(ctx, k, g);
        if (r != w)
            return 0;
    }
    return 1;
}

/* Verify child geometry: exit constraints for Hilbert curve construction */
static int verify_child_geometry(hilbert_tables_ctx_t *ctx, int k)
{
    uint32_t size = 1u << k;

    /* Entry of first cube should be 0 */
    if (hilbert_child_entry(ctx, k, 0) != 0)
        return 0;

    /* All child_dir values should be in [0, k-1] */
    for (uint32_t w = 0; w < size; w++)
    {
        uint8_t dir = hilbert_child_dir(ctx, k, w);
        if (dir >= (uint8_t)k)
            return 0;
    }

    /* The "mismatch state" s_w = gray[w] XOR child_entry[w] should satisfy:
       - s_0 = 0 (entry of first cube is gray[0] = 0)
       - For each transition w -> w+1, the bit at position d_w (where gray[w+1] = gray[w] XOR e_{d_w})
         must be set in s_{w+1}
       - s_{last} has Hamming weight 1
    */

    /* Check s_0 = 0 */
    uint8_t g0 = hilbert_gray(ctx, k, 0);
    uint8_t e0 = hilbert_child_entry(ctx, k, 0);
    if ((g0 ^ e0) != 0)
        return 0;

    /* Check transition constraints */
    for (uint32_t w = 0; w + 1 < size; w++)
    {
        uint8_t g_curr = hilbert_gray(ctx, k, w);
        uint8_t g_next = hilbert_gray(ctx, k, w + 1);
        uint8_t diff = g_curr ^ g_next;

        /* diff should be a single bit */
        if (diff == 0 || (diff & (diff - 1)) != 0)
            return 0;

        /* Find the transition dimension d_w */
        int d_w = 0;
        while (((diff >> d_w) & 1) == 0)
            d_w++;

        /* s_{w+1} should have bit d_w set */
        uint8_t s_next = g_next ^ hilbert_child_entry(ctx, k, w + 1);
        if (((s_next >> d_w) & 1) == 0)
            return 0;
    }

    /* Check s_{last} has Hamming weight 1 */
    uint8_t g_last = hilbert_gray(ctx, k, size - 1);
    uint8_t e_last = hilbert_child_entry(ctx, k, size - 1);
    uint8_t s_last = g_last ^ e_last;
    int popcount = 0;
    for (int b = 0; b < 8; b++)
    {
        if ((s_last >> b) & 1)
            popcount++;
    }
    if (popcount != 1)
        return 0;

    return 1;
}

int main(int argc, char *argv[])
{
    if (argc != 4)
    {
        fprintf(stderr, "Usage: %s FILE.h5 NAME INDEX\n", argv[0]);
        return 1;
    }

    const char *filename = argv[1];
    const char *name = argv[2];
    int index = atoi(argv[3]);

    hilbert_tables_ctx_t *ctx = hilbert_tables_open(filename);
    if (!ctx)
    {
        fprintf(stderr, "Failed to open %s\n", filename);
        return 1;
    }

    int count = hilbert_tables_count(ctx, name);
    if (count == 0)
    {
        fprintf(stderr, "No tables found for name '%s'\n", name);
        hilbert_tables_close(ctx);
        return 1;
    }
    printf("Found %d table set(s) for '%s'\n", count, name);

    if (hilbert_tables_select(ctx, name, index) < 0)
    {
        fprintf(stderr, "Failed to select %s/%d\n", name, index);
        hilbert_tables_close(ctx);
        return 1;
    }

    int all_passed = 1;

    printf("Verifying tables for %s/%d:\n", name, index);
    for (int k = 1; k <= 8; k++)
    {
        printf("  k=%d: ", k);
        fflush(stdout);

        int gray_ok = verify_gray_code(ctx, k);
        int rank_ok = verify_gray_rank(ctx, k);
        int geom_ok = verify_child_geometry(ctx, k);

        if (gray_ok && rank_ok && geom_ok)
        {
            /* Check if this is the standard Hamilton geometry for BRGC */
            int is_std = 1;
            uint32_t size = 1u << k;
            for (uint32_t w = 0; w < size && is_std; w++)
            {
                if (hilbert_gray(ctx, k, w) != brgc((uint8_t)w))
                    is_std = 0;
                if (hilbert_child_entry(ctx, k, w) != child_entry_std(w))
                    is_std = 0;
                if (hilbert_child_dir(ctx, k, w) != child_dir_std(w, k))
                    is_std = 0;
            }
            printf("OK (standard=%s)\n", is_std ? "yes" : "no");
        }
        else
        {
            printf("FAIL");
            if (!gray_ok)
                printf(" [gray]");
            if (!rank_ok)
                printf(" [gray_rank]");
            if (!geom_ok)
                printf(" [geometry]");
            printf("\n");
            all_passed = 0;
        }
    }

    hilbert_tables_close(ctx);

    if (all_passed)
    {
        printf("All verifications passed.\n");
        return 0;
    }
    else
    {
        printf("Some verifications failed.\n");
        return 1;
    }
}
