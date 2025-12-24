/**
 * Test harness comparing handwritten C Hilbert implementation against
 * Lean's verified implementation.
 *
 * This program runs encode/decode operations through both implementations
 * and reports any discrepancies.
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdbool.h>

/* Include the Lean FFI wrapper */
#include "../lean/ffi/hilbert_ffi.h"

/* Declarations for the handwritten C implementation */
typedef uint32_t coord_t;

extern uint64_t hilbert_encode_64(const coord_t *point, const int *m, int n);
extern void hilbert_decode_64(uint64_t h, const int *m, int n, coord_t *point);

/* Test statistics */
static int g_tests_run = 0;
static int g_tests_passed = 0;
static int g_tests_failed = 0;

/**
 * Test roundtrip: encode then decode should return original point
 */
static bool test_roundtrip(uint32_t n_dims, const uint32_t* coords, const uint32_t* exponents) {
    uint64_t h_lean = hilbert_lean_encode(n_dims, coords, exponents);

    uint32_t decoded[32];
    int rc = hilbert_lean_decode(n_dims, exponents, h_lean, decoded);

    if (rc != 0) {
        printf("  FAIL: Lean decode returned error\n");
        return false;
    }

    for (uint32_t i = 0; i < n_dims; i++) {
        if (decoded[i] != coords[i]) {
            printf("  FAIL: Lean roundtrip mismatch at dim %u: expected %u, got %u\n",
                   i, coords[i], decoded[i]);
            return false;
        }
    }
    return true;
}

/**
 * Test that Lean and C implementations produce the same results
 */
static bool test_lean_vs_c(uint32_t n_dims, const uint32_t* coords, const uint32_t* exponents) {
    /* Call Lean encode */
    uint64_t h_lean = hilbert_lean_encode(n_dims, coords, exponents);

    /* Call C encode - need to convert exponents to int* */
    int exp_int[32];
    for (uint32_t i = 0; i < n_dims; i++) {
        exp_int[i] = (int)exponents[i];
    }
    uint64_t h_c = hilbert_encode_64(coords, exp_int, (int)n_dims);

    if (h_lean != h_c) {
        printf("  FAIL: Encode mismatch - Lean: %llu, C: %llu\n",
               (unsigned long long)h_lean, (unsigned long long)h_c);
        printf("        coords: [");
        for (uint32_t i = 0; i < n_dims; i++) {
            printf("%u%s", coords[i], i < n_dims-1 ? ", " : "");
        }
        printf("], exponents: [");
        for (uint32_t i = 0; i < n_dims; i++) {
            printf("%u%s", exponents[i], i < n_dims-1 ? ", " : "");
        }
        printf("]\n");
        return false;
    }

    /* Test decode */
    uint32_t decoded_lean[32], decoded_c[32];

    int rc = hilbert_lean_decode(n_dims, exponents, h_lean, decoded_lean);
    if (rc != 0) {
        printf("  FAIL: Lean decode returned error for h=%llu\n", (unsigned long long)h_lean);
        return false;
    }

    hilbert_decode_64(h_c, exp_int, (int)n_dims, decoded_c);

    for (uint32_t i = 0; i < n_dims; i++) {
        if (decoded_lean[i] != decoded_c[i]) {
            printf("  FAIL: Decode mismatch at dim %u - Lean: %u, C: %u (h=%llu)\n",
                   i, decoded_lean[i], decoded_c[i], (unsigned long long)h_lean);
            return false;
        }
    }

    return true;
}

/**
 * Run a test case
 */
static void run_test(const char* name, uint32_t n_dims, const uint32_t* coords, const uint32_t* exponents) {
    g_tests_run++;

    printf("Test: %s... ", name);
    fflush(stdout);

    bool roundtrip_ok = test_roundtrip(n_dims, coords, exponents);
    bool compare_ok = test_lean_vs_c(n_dims, coords, exponents);

    if (roundtrip_ok && compare_ok) {
        printf("PASS\n");
        g_tests_passed++;
    } else {
        g_tests_failed++;
    }
}

/**
 * Exhaustive test: test all points in a small grid
 */
static void exhaustive_test_2d(uint32_t m0, uint32_t m1) {
    printf("\nExhaustive 2D test (%u x %u = %llu points)...\n",
           1u << m0, 1u << m1, (unsigned long long)(1ull << (m0 + m1)));

    uint32_t exponents[] = {m0, m1};
    uint32_t coords[2];
    int errors = 0;
    uint64_t total = 1ull << (m0 + m1);

    for (uint32_t x = 0; x < (1u << m0) && errors < 10; x++) {
        for (uint32_t y = 0; y < (1u << m1) && errors < 10; y++) {
            coords[0] = x;
            coords[1] = y;

            g_tests_run++;
            if (!test_lean_vs_c(2, coords, exponents)) {
                errors++;
                g_tests_failed++;
            } else {
                g_tests_passed++;
            }
        }
    }

    if (errors == 0) {
        printf("  All %llu points passed!\n", total);
    } else {
        printf("  %d errors (stopped after 10)\n", errors);
    }
}

/**
 * Exhaustive test: test all Hilbert indices in a small grid
 */
static void exhaustive_decode_test_2d(uint32_t m0, uint32_t m1) {
    printf("\nExhaustive decode test (%u x %u)...\n", 1u << m0, 1u << m1);

    uint32_t exponents[] = {m0, m1};
    int errors = 0;
    uint64_t total = 1ull << (m0 + m1);

    for (uint64_t h = 0; h < total && errors < 10; h++) {
        g_tests_run++;

        uint32_t decoded_lean[2], decoded_c[2];
        int exp_int[] = {(int)m0, (int)m1};

        int rc = hilbert_lean_decode(2, exponents, h, decoded_lean);
        hilbert_decode_64(h, exp_int, 2, decoded_c);

        if (rc != 0) {
            printf("  FAIL: Lean decode error at h=%llu\n", (unsigned long long)h);
            errors++;
            g_tests_failed++;
            continue;
        }

        if (decoded_lean[0] != decoded_c[0] || decoded_lean[1] != decoded_c[1]) {
            printf("  FAIL: Decode mismatch at h=%llu - Lean: (%u,%u), C: (%u,%u)\n",
                   (unsigned long long)h,
                   decoded_lean[0], decoded_lean[1],
                   decoded_c[0], decoded_c[1]);
            errors++;
            g_tests_failed++;
        } else {
            g_tests_passed++;
        }
    }

    if (errors == 0) {
        printf("  All %llu indices passed!\n", total);
    }
}

int main(int argc, char** argv) {
    printf("=== Hilbert Curve: Lean vs C Implementation Test ===\n\n");

    /* Initialize Lean runtime */
    printf("Initializing Lean runtime...\n");
    if (hilbert_lean_init() != 0) {
        fprintf(stderr, "Failed to initialize Lean runtime!\n");
        return 1;
    }
    printf("Lean runtime initialized.\n\n");

    /* Basic tests */
    printf("=== Basic Tests ===\n");

    /* Test 1: Simple 2D case */
    {
        uint32_t coords[] = {0, 0};
        uint32_t exponents[] = {3, 3};
        run_test("2D origin (0,0) with 8x8 grid", 2, coords, exponents);
    }

    {
        uint32_t coords[] = {1, 0};
        uint32_t exponents[] = {3, 3};
        run_test("2D (1,0) with 8x8 grid", 2, coords, exponents);
    }

    {
        uint32_t coords[] = {7, 7};
        uint32_t exponents[] = {3, 3};
        run_test("2D (7,7) with 8x8 grid", 2, coords, exponents);
    }

    /* Test 2: Anisotropic 2D case */
    {
        uint32_t coords[] = {3, 1};
        uint32_t exponents[] = {3, 2};  /* 8x4 grid */
        run_test("2D anisotropic (3,1) with 8x4 grid", 2, coords, exponents);
    }

    /* Test 3: 3D case */
    {
        uint32_t coords[] = {1, 2, 3};
        uint32_t exponents[] = {3, 3, 3};
        run_test("3D (1,2,3) with 8x8x8 grid", 3, coords, exponents);
    }

    /* Test 4: Higher dimensional */
    {
        uint32_t coords[] = {1, 1, 1, 1};
        uint32_t exponents[] = {2, 2, 2, 2};
        run_test("4D (1,1,1,1) with 4^4 grid", 4, coords, exponents);
    }

    /* Exhaustive tests */
    printf("\n=== Exhaustive Tests ===\n");
    exhaustive_test_2d(3, 3);      /* 8x8 = 64 points */
    exhaustive_decode_test_2d(3, 3);
    exhaustive_test_2d(4, 3);      /* 16x8 = 128 points (anisotropic) */
    exhaustive_test_2d(3, 4);      /* 8x16 = 128 points (anisotropic, reversed) */

    /* Summary */
    printf("\n=== Summary ===\n");
    printf("Tests run: %d\n", g_tests_run);
    printf("Passed: %d\n", g_tests_passed);
    printf("Failed: %d\n", g_tests_failed);

    /* Cleanup */
    hilbert_lean_finalize();

    return g_tests_failed > 0 ? 1 : 0;
}
