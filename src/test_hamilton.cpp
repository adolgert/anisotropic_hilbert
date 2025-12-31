/*
 * test_hamilton.cpp
 *
 * Test harness for hamilton.c - Hamilton's Compact Hilbert Index implementation.
 *
 * Tests:
 * 1. Roundtrip: decode(encode(p)) == p for all points
 * 2. Adjacency: consecutive indices map to adjacent points (L1 distance = 1)
 *    NOTE: Adjacency is only tested when all extents are equal, since Hamilton's
 *    algorithm has a bug that causes discontinuities for anisotropic boxes.
 */

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <algorithm>

/* Include the implementation directly for testing */
extern "C" {
#include "hamilton.c"
}

static int g_verbose = 0;

/* Test encode/decode roundtrip for all indices in a given shape */
static int test_roundtrip(int n, const int *m, const char *label)
{
    int errors = 0;
    int total_bits = 0;
    for (int i = 0; i < n; i++)
        total_bits += m[i];

    hamilton_index_t max_h = ((hamilton_index_t)1 << total_bits);
    /* Limit iterations for large spaces */
    if (total_bits >= 20)
        max_h = 10000;

    for (hamilton_index_t h = 0; h < max_h; h++)
    {
        hamilton_coord_t point[HAMILTON_MAX_DIMS];
        hamilton_decode(h, m, n, point);
        hamilton_index_t h2 = hamilton_encode(point, m, n);
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

    hamilton_index_t max_h = ((hamilton_index_t)1 << total_bits);
    if (total_bits >= 20)
        max_h = 10000;

    for (hamilton_index_t h = 0; h + 1 < max_h; h++)
    {
        hamilton_coord_t p1[HAMILTON_MAX_DIMS], p2[HAMILTON_MAX_DIMS];
        hamilton_decode(h, m, n, p1);
        hamilton_decode(h + 1, m, n, p2);

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
                printf("    p1=(");
                for (int i = 0; i < n; i++)
                    printf("%u%s", p1[i], i < n - 1 ? "," : "");
                printf(") p2=(");
                for (int i = 0; i < n; i++)
                    printf("%u%s", p2[i], i < n - 1 ? "," : "");
                printf(")\n");
            }
        }
    }

    if (g_verbose && errors > 0)
        printf("%s: FAIL (%d errors)\n", label, errors);

    return errors;
}

/* Count discontinuities (for reporting purposes) */
static int count_discontinuities(int n, const int *m)
{
    int total_bits = 0;
    for (int i = 0; i < n; i++)
        total_bits += m[i];

    hamilton_index_t max_h = ((hamilton_index_t)1 << total_bits);
    if (total_bits >= 20)
        max_h = 10000;

    int discontinuities = 0;
    for (hamilton_index_t h = 0; h + 1 < max_h; h++)
    {
        hamilton_coord_t p1[HAMILTON_MAX_DIMS], p2[HAMILTON_MAX_DIMS];
        hamilton_decode(h, m, n, p1);
        hamilton_decode(h + 1, m, n, p2);

        int dist = 0;
        for (int i = 0; i < n; i++)
        {
            int d = (int)p2[i] - (int)p1[i];
            dist += (d < 0) ? -d : d;
        }

        if (dist != 1)
            discontinuities++;
    }
    return discontinuities;
}

int main(int argc, char **argv)
{
    g_verbose = (argc > 1 && strcmp(argv[1], "-v") == 0);

    printf("Testing Hamilton's Compact Hilbert Index (with known bug)\n");
    printf("=========================================================\n\n");

    int total_tests = 0;
    int total_errors = 0;

    /* ====================================================================== */
    /* Roundtrip tests - these should always pass                             */
    /* ====================================================================== */
    printf("Roundtrip tests (encode/decode consistency):\n");

    /* 2D tests */
    {
        int m[] = {2, 2};
        total_errors += test_roundtrip(2, m, "  2D [2,2]");
        total_tests++;
    }
    {
        int m[] = {3, 2};
        total_errors += test_roundtrip(2, m, "  2D [3,2]");
        total_tests++;
    }
    {
        int m[] = {4, 3};
        total_errors += test_roundtrip(2, m, "  2D [4,3]");
        total_tests++;
    }
    {
        int m[] = {2, 1};
        total_errors += test_roundtrip(2, m, "  2D [2,1]");
        total_tests++;
    }

    /* 3D tests */
    {
        int m[] = {2, 2, 2};
        total_errors += test_roundtrip(3, m, "  3D [2,2,2]");
        total_tests++;
    }
    {
        int m[] = {3, 2, 2};
        total_errors += test_roundtrip(3, m, "  3D [3,2,2]");
        total_tests++;
    }
    {
        int m[] = {3, 3, 2};
        total_errors += test_roundtrip(3, m, "  3D [3,3,2]");
        total_tests++;
    }

    /* 4D tests */
    {
        int m[] = {2, 2, 2, 2};
        total_errors += test_roundtrip(4, m, "  4D [2,2,2,2]");
        total_tests++;
    }
    {
        int m[] = {3, 2, 2, 2};
        total_errors += test_roundtrip(4, m, "  4D [3,2,2,2]");
        total_tests++;
    }

    /* 5D tests */
    {
        int m[] = {2, 2, 2, 2, 2};
        total_errors += test_roundtrip(5, m, "  5D [2,2,2,2,2]");
        total_tests++;
    }

    /* 6D tests */
    {
        int m[] = {2, 2, 2, 2, 2, 2};
        total_errors += test_roundtrip(6, m, "  6D [2,2,2,2,2,2]");
        total_tests++;
    }

    /* 7D tests */
    {
        int m[] = {2, 2, 2, 2, 2, 2, 2};
        total_errors += test_roundtrip(7, m, "  7D [2,2,2,2,2,2,2]");
        total_tests++;
    }

    /* 8D test */
    {
        int m[] = {2, 2, 2, 2, 2, 2, 2, 2};
        total_errors += test_roundtrip(8, m, "  8D [2,2,2,2,2,2,2,2]");
        total_tests++;
    }

    printf("  %d roundtrip tests, %d errors\n\n", total_tests, total_errors);

    /* ====================================================================== */
    /* Adjacency tests - only for isotropic boxes (equal extents)             */
    /* ====================================================================== */
    printf("Adjacency tests (only for equal extents - Hamilton bug otherwise):\n");

    int adj_tests = 0;
    int adj_errors = 0;

    /* 2D isotropic */
    for (int k = 1; k <= 5; k++)
    {
        int m[] = {k, k};
        char label[64];
        snprintf(label, sizeof(label), "  2D [%d,%d]", k, k);
        adj_errors += test_adjacency(2, m, label);
        adj_tests++;
    }

    /* 3D isotropic */
    for (int k = 1; k <= 4; k++)
    {
        int m[] = {k, k, k};
        char label[64];
        snprintf(label, sizeof(label), "  3D [%d,%d,%d]", k, k, k);
        adj_errors += test_adjacency(3, m, label);
        adj_tests++;
    }

    /* 4D isotropic */
    for (int k = 1; k <= 3; k++)
    {
        int m[] = {k, k, k, k};
        char label[64];
        snprintf(label, sizeof(label), "  4D [%d,%d,%d,%d]", k, k, k, k);
        adj_errors += test_adjacency(4, m, label);
        adj_tests++;
    }

    /* 5D isotropic */
    for (int k = 1; k <= 2; k++)
    {
        int m[] = {k, k, k, k, k};
        char label[64];
        snprintf(label, sizeof(label), "  5D [%d,%d,%d,%d,%d]", k, k, k, k, k);
        adj_errors += test_adjacency(5, m, label);
        adj_tests++;
    }

    /* 6D isotropic */
    {
        int m[] = {2, 2, 2, 2, 2, 2};
        adj_errors += test_adjacency(6, m, "  6D [2,2,2,2,2,2]");
        adj_tests++;
    }

    printf("  %d adjacency tests, %d errors\n\n", adj_tests, adj_errors);

    total_tests += adj_tests;
    total_errors += adj_errors;

    /* ====================================================================== */
    /* Demonstrate the bug: show discontinuities in anisotropic boxes         */
    /* ====================================================================== */
    printf("Bug demonstration (discontinuities in anisotropic boxes):\n");

    struct {
        int n;
        int m[8];
        const char *label;
    } aniso_cases[] = {
        {2, {2, 1, 0, 0, 0, 0, 0, 0}, "2D [2,1] (4x2)"},
        {2, {3, 2, 0, 0, 0, 0, 0, 0}, "2D [3,2] (8x4)"},
        {2, {4, 2, 0, 0, 0, 0, 0, 0}, "2D [4,2] (16x4)"},
        {3, {3, 2, 1, 0, 0, 0, 0, 0}, "3D [3,2,1] (8x4x2)"},
        {3, {3, 2, 2, 0, 0, 0, 0, 0}, "3D [3,2,2] (8x4x4)"},
        {4, {3, 2, 2, 1, 0, 0, 0, 0}, "4D [3,2,2,1]"},
    };

    for (size_t i = 0; i < sizeof(aniso_cases) / sizeof(aniso_cases[0]); i++)
    {
        int disc = count_discontinuities(aniso_cases[i].n, aniso_cases[i].m);
        printf("  %s: %d discontinuities\n", aniso_cases[i].label, disc);
    }

    printf("\n");

    /* ====================================================================== */
    /* Summary                                                                */
    /* ====================================================================== */
    printf("=== Summary ===\n");
    if (total_errors == 0)
    {
        printf("All %d tests passed.\n", total_tests);
        printf("(Note: Adjacency only tested for isotropic boxes due to Hamilton bug)\n");
        return 0;
    }
    else
    {
        printf("FAILED: %d errors in %d tests\n", total_errors, total_tests);
        return 1;
    }
}
