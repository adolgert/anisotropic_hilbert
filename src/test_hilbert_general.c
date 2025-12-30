/*
 * test_hilbert_general.c
 *
 * Test harness for hilbert_general.c which uses table-based lookups
 * for Gray codes and child geometry. Tests all curve types from HDF5.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Include the implementation directly for testing */
#include "hilbert_general.c"

static int g_verbose = 0;

/* Test encode/decode roundtrip for all indices in a given shape */
static int test_roundtrip(int n, const int *m, const char *label)
{
    int errors = 0;
    int total_bits = 0;
    for (int i = 0; i < n; i++)
        total_bits += m[i];

    hindex_t max_h = ((hindex_t)1 << total_bits);
    /* Limit iterations for large spaces */
    if (total_bits >= 20)
        max_h = 10000;

    for (hindex_t h = 0; h < max_h; h++)
    {
        coord_t point[MAX_DIMS];
        hilbert_affine_decode(h, m, n, point);
        hindex_t h2 = hilbert_affine_encode(point, m, n);
        if (h != h2)
        {
            errors++;
            if (g_verbose)
            {
                printf("  FAIL: h=%llu -> point=(", (unsigned long long)h);
                for (int i = 0; i < n; i++)
                {
                    printf("%u%s", point[i], i < n - 1 ? "," : "");
                }
                printf(") -> h2=%llu\n", (unsigned long long)h2);
            }
        }
    }

    if (g_verbose || errors > 0)
    {
        printf("%s: %s", label, errors == 0 ? "PASS" : "FAIL");
        if (errors > 0)
            printf(" (%d errors)", errors);
        printf("\n");
    }

    return errors;
}

/* Test that adjacent Hilbert indices map to adjacent coordinates */
static int test_adjacency(int n, const int *m, const char *label)
{
    int errors = 0;
    int total_bits = 0;
    for (int i = 0; i < n; i++)
        total_bits += m[i];

    hindex_t max_h = ((hindex_t)1 << total_bits);
    if (total_bits >= 20)
        max_h = 10000;

    for (hindex_t h = 0; h + 1 < max_h; h++)
    {
        coord_t p1[MAX_DIMS], p2[MAX_DIMS];
        hilbert_affine_decode(h, m, n, p1);
        hilbert_affine_decode(h + 1, m, n, p2);

        /* Count Manhattan distance */
        int dist = 0;
        for (int i = 0; i < n; i++)
        {
            int d = (int)p2[i] - (int)p1[i];
            dist += (d < 0) ? -d : d;
        }

        if (dist != 1)
        {
            errors++;
            if (g_verbose)
            {
                printf("  FAIL: h=%llu and h+1=%llu have distance %d\n",
                       (unsigned long long)h, (unsigned long long)(h + 1), dist);
            }
        }
    }

    if (g_verbose && errors > 0)
        printf("%s: FAIL (%d errors)\n", label, errors);

    return errors;
}

/* Run all tests for current table set */
static int run_tests(void)
{
    int total_tests = 0;
    int total_errors = 0;

    printf("  Roundtrip tests: ");
    fflush(stdout);

    /* 2D tests */
    {
        int m[] = {2, 2};
        total_errors += test_roundtrip(2, m, "2D [2,2]");
        total_tests++;
    }
    {
        int m[] = {3, 2};
        total_errors += test_roundtrip(2, m, "2D [3,2]");
        total_tests++;
    }
    {
        int m[] = {4, 3};
        total_errors += test_roundtrip(2, m, "2D [4,3]");
        total_tests++;
    }

    /* 3D tests */
    {
        int m[] = {2, 2, 2};
        total_errors += test_roundtrip(3, m, "3D [2,2,2]");
        total_tests++;
    }
    {
        int m[] = {3, 2, 2};
        total_errors += test_roundtrip(3, m, "3D [3,2,2]");
        total_tests++;
    }
    {
        int m[] = {3, 3, 2};
        total_errors += test_roundtrip(3, m, "3D [3,3,2]");
        total_tests++;
    }

    /* 4D tests */
    {
        int m[] = {2, 2, 2, 2};
        total_errors += test_roundtrip(4, m, "4D [2,2,2,2]");
        total_tests++;
    }
    {
        int m[] = {3, 2, 2, 2};
        total_errors += test_roundtrip(4, m, "4D [3,2,2,2]");
        total_tests++;
    }

    /* 5D tests */
    {
        int m[] = {2, 2, 2, 2, 2};
        total_errors += test_roundtrip(5, m, "5D [2,2,2,2,2]");
        total_tests++;
    }
    {
        int m[] = {3, 2, 2, 2, 2};
        total_errors += test_roundtrip(5, m, "5D [3,2,2,2,2]");
        total_tests++;
    }

    /* 6D tests */
    {
        int m[] = {2, 2, 2, 2, 2, 2};
        total_errors += test_roundtrip(6, m, "6D [2,2,2,2,2,2]");
        total_tests++;
    }

    /* 7D tests */
    {
        int m[] = {2, 2, 2, 2, 2, 2, 2};
        total_errors += test_roundtrip(7, m, "7D [2,2,2,2,2,2,2]");
        total_tests++;
    }

    /* 8D test */
    {
        int m[] = {2, 2, 2, 2, 2, 2, 2, 2};
        total_errors += test_roundtrip(8, m, "8D [2,2,2,2,2,2,2,2]");
        total_tests++;
    }

    printf("%d tests, %d errors\n", total_tests, total_errors);

    printf("  Adjacency tests: ");
    fflush(stdout);

    int adj_tests = 0;
    int adj_errors = 0;

    /* Adjacency tests - verify space-filling property */
    {
        int m[] = {3, 3};
        for (int i = 1; i < 10; i++)
        {
            for (int j = 1; j < 10; j++)
            {
                m[0] = i;
                m[1] = j;
                adj_errors += test_adjacency(2, m, "2D");
                adj_tests++;
            }
        }
    }
    {
        int m[] = {2, 2, 2};
        adj_errors += test_adjacency(3, m, "3D [2,2,2]");
        adj_tests++;
    }
    {
        int limit = 4;  /* Reduced from 6 to speed up tests */
        int m[] = {2, 2, 2, 2};
        for (int i = 1; i < limit; i++)
        {
            for (int j = 1; j < limit; j++)
            {
                for (int k = 1; k < limit; k++)
                {
                    for (int l = 1; l < limit; l++)
                    {
                        m[0] = i;
                        m[1] = j;
                        m[2] = k;
                        m[3] = l;
                        adj_errors += test_adjacency(4, m, "4D");
                        adj_tests++;
                    }
                }
            }
        }
    }

    printf("%d tests, %d errors\n", adj_tests, adj_errors);

    total_tests += adj_tests;
    total_errors += adj_errors;

    return total_errors;
}

int main(int argc, char **argv)
{
    g_verbose = (argc > 1 && strcmp(argv[1], "-v") == 0);

    const char *hdf5_file = "hilbert_tables.h5";
    const char *types[] = {"brgc", "monotone", "balanced", "random"};
    int num_types = 4;

    /* Initialize with first table type */
    if (hilbert_tables_init(hdf5_file, types[0], 0) < 0)
    {
        fprintf(stderr, "Failed to open %s\n", hdf5_file);
        fprintf(stderr, "Run 'make hilbert_tables.h5' first to generate the tables.\n");
        return 1;
    }

    int total_errors = 0;

    printf("Testing Hilbert curves from %s\n\n", hdf5_file);

    for (int t = 0; t < num_types; t++)
    {
        printf("=== %s (index 0) ===\n", types[t]);

        if (t > 0)
        {
            if (hilbert_tables_switch(types[t], 0) < 0)
            {
                fprintf(stderr, "Failed to switch to %s/0\n", types[t]);
                total_errors++;
                continue;
            }
        }

        total_errors += run_tests();
        printf("\n");
    }

    hilbert_tables_cleanup();

    printf("=== Final Summary ===\n");
    if (total_errors == 0)
    {
        printf("All tests passed for all curve types.\n");
        return 0;
    }
    else
    {
        printf("Total errors: %d\n", total_errors);
        return 1;
    }
}
