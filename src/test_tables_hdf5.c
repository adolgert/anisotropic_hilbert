/*
 * test_tables_hdf5.c
 *
 * Test harness for HDF5-based Hilbert table storage.
 */

#include "tables_hdf5.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define TEST_FILE "test_hilbert_tables.h5"

static int tests_run = 0;
static int tests_passed = 0;

#define TEST(name) do { \
    printf("  %s... ", #name); \
    fflush(stdout); \
    tests_run++; \
    if (test_##name()) { \
        printf("PASS\n"); \
        tests_passed++; \
    } else { \
        printf("FAIL\n"); \
    } \
} while(0)

/* Generate random table data for dimension k */
static void generate_random_tables(int k, uint8_t* gray, uint8_t* gray_rank,
                                   uint8_t* child_entry, uint8_t* child_dir)
{
    uint32_t size = 1u << k;

    /* Generate a random permutation for gray code */
    for (uint32_t i = 0; i < size; i++) {
        gray[i] = (uint8_t)i;
    }
    for (uint32_t i = size - 1; i > 0; i--) {
        uint32_t j = (uint32_t)rand() % (i + 1);
        uint8_t tmp = gray[i];
        gray[i] = gray[j];
        gray[j] = tmp;
    }

    /* gray_rank is inverse of gray */
    for (uint32_t i = 0; i < size; i++) {
        gray_rank[gray[i]] = (uint8_t)i;
    }

    /* Random child_entry and child_dir */
    for (uint32_t i = 0; i < size; i++) {
        child_entry[i] = (uint8_t)(rand() % size);
        child_dir[i] = (uint8_t)(rand() % k);
    }
}

/* Test basic create/close cycle */
static int test_create_close(void)
{
    hilbert_tables_ctx_t* ctx = hilbert_tables_create(TEST_FILE);
    if (!ctx) return 0;
    hilbert_tables_close(ctx);
    return 1;
}

/* Test storing and retrieving tables */
static int test_store_retrieve(void)
{
    uint8_t gray[128], gray_rank[128], child_entry[128], child_dir[128];
    uint8_t read_gray[128], read_gray_rank[128], read_child_entry[128], read_child_dir[128];

    /* Create file and store tables for k=3 */
    hilbert_tables_ctx_t* ctx = hilbert_tables_create(TEST_FILE);
    if (!ctx) return 0;

    generate_random_tables(3, gray, gray_rank, child_entry, child_dir);

    if (hilbert_tables_add(ctx, "test", 0, 3, gray, gray_rank, child_entry, child_dir) < 0) {
        hilbert_tables_close(ctx);
        return 0;
    }

    hilbert_tables_close(ctx);

    /* Reopen and read back */
    ctx = hilbert_tables_open(TEST_FILE);
    if (!ctx) return 0;

    if (hilbert_tables_select(ctx, "test", 0) < 0) {
        hilbert_tables_close(ctx);
        return 0;
    }

    /* Read all values */
    for (uint32_t w = 0; w < 8; w++) {
        read_gray[w] = hilbert_gray(ctx, 3, w);
        read_gray_rank[w] = hilbert_gray_rank(ctx, 3, w);
        read_child_entry[w] = hilbert_child_entry(ctx, 3, w);
        read_child_dir[w] = hilbert_child_dir(ctx, 3, w);
    }

    hilbert_tables_close(ctx);

    /* Verify */
    for (uint32_t w = 0; w < 8; w++) {
        if (read_gray[w] != gray[w]) return 0;
        if (read_gray_rank[w] != gray_rank[w]) return 0;
        if (read_child_entry[w] != child_entry[w]) return 0;
        if (read_child_dir[w] != child_dir[w]) return 0;
    }

    return 1;
}

/* Test storing multiple k values */
static int test_multiple_k(void)
{
    uint8_t gray[128], gray_rank[128], child_entry[128], child_dir[128];

    /* Create file and store tables for k=1..7 */
    hilbert_tables_ctx_t* ctx = hilbert_tables_create(TEST_FILE);
    if (!ctx) return 0;

    for (int k = 1; k <= 7; k++) {
        generate_random_tables(k, gray, gray_rank, child_entry, child_dir);
        if (hilbert_tables_add(ctx, "multi", 0, k, gray, gray_rank, child_entry, child_dir) < 0) {
            hilbert_tables_close(ctx);
            return 0;
        }
    }

    hilbert_tables_close(ctx);

    /* Reopen and verify we can read each k */
    ctx = hilbert_tables_open(TEST_FILE);
    if (!ctx) return 0;

    if (hilbert_tables_select(ctx, "multi", 0) < 0) {
        hilbert_tables_close(ctx);
        return 0;
    }

    /* Just check that we can read without error */
    for (int k = 1; k <= 7; k++) {
        uint32_t size = 1u << k;
        for (uint32_t w = 0; w < size; w++) {
            (void)hilbert_gray(ctx, (uint32_t)k, w);
        }
    }

    hilbert_tables_close(ctx);
    return 1;
}

/* Test count function */
static int test_count(void)
{
    uint8_t gray[4] = {0, 1, 2, 3};
    uint8_t gray_rank[4] = {0, 1, 2, 3};
    uint8_t child_entry[4] = {0, 0, 0, 0};
    uint8_t child_dir[4] = {0, 1, 0, 1};

    hilbert_tables_ctx_t* ctx = hilbert_tables_create(TEST_FILE);
    if (!ctx) return 0;

    /* Add 3 sets under "counted" */
    for (int i = 0; i < 3; i++) {
        if (hilbert_tables_add(ctx, "counted", i, 2, gray, gray_rank, child_entry, child_dir) < 0) {
            hilbert_tables_close(ctx);
            return 0;
        }
    }

    hilbert_tables_close(ctx);

    /* Reopen and count */
    ctx = hilbert_tables_open(TEST_FILE);
    if (!ctx) return 0;

    int count = hilbert_tables_count(ctx, "counted");
    hilbert_tables_close(ctx);

    return (count == 3);
}

/* Test count for nonexistent name */
static int test_count_nonexistent(void)
{
    hilbert_tables_ctx_t* ctx = hilbert_tables_open(TEST_FILE);
    if (!ctx) return 0;

    int count = hilbert_tables_count(ctx, "nonexistent_name");
    hilbert_tables_close(ctx);

    return (count == 0);
}

/* Test select with invalid name/index */
static int test_select_invalid(void)
{
    hilbert_tables_ctx_t* ctx = hilbert_tables_open(TEST_FILE);
    if (!ctx) return 0;

    int result = hilbert_tables_select(ctx, "nonexistent", 0);
    hilbert_tables_close(ctx);

    return (result < 0);
}

/* Test auto-load when k changes */
static int test_auto_load(void)
{
    uint8_t gray2[4], gray_rank2[4], child_entry2[4], child_dir2[4];
    uint8_t gray3[8], gray_rank3[8], child_entry3[8], child_dir3[8];

    generate_random_tables(2, gray2, gray_rank2, child_entry2, child_dir2);
    generate_random_tables(3, gray3, gray_rank3, child_entry3, child_dir3);

    hilbert_tables_ctx_t* ctx = hilbert_tables_create(TEST_FILE);
    if (!ctx) return 0;

    hilbert_tables_add(ctx, "autoload", 0, 2, gray2, gray_rank2, child_entry2, child_dir2);
    hilbert_tables_add(ctx, "autoload", 0, 3, gray3, gray_rank3, child_entry3, child_dir3);

    hilbert_tables_close(ctx);

    /* Reopen and switch between k values */
    ctx = hilbert_tables_open(TEST_FILE);
    if (!ctx) return 0;

    hilbert_tables_select(ctx, "autoload", 0);

    /* Access k=2 */
    uint8_t v2 = hilbert_gray(ctx, 2, 0);
    if (v2 != gray2[0]) {
        hilbert_tables_close(ctx);
        return 0;
    }

    /* Access k=3 (should auto-load) */
    uint8_t v3 = hilbert_gray(ctx, 3, 0);
    if (v3 != gray3[0]) {
        hilbert_tables_close(ctx);
        return 0;
    }

    /* Access k=2 again (should auto-load again) */
    v2 = hilbert_gray(ctx, 2, 1);
    if (v2 != gray2[1]) {
        hilbert_tables_close(ctx);
        return 0;
    }

    hilbert_tables_close(ctx);
    return 1;
}

/* Test overwriting existing table */
static int test_overwrite(void)
{
    uint8_t gray1[4] = {0, 1, 2, 3};
    uint8_t gray2[4] = {3, 2, 1, 0};
    uint8_t dummy[4] = {0, 0, 0, 0};

    hilbert_tables_ctx_t* ctx = hilbert_tables_create(TEST_FILE);
    if (!ctx) return 0;

    /* Write first version */
    hilbert_tables_add(ctx, "overwrite", 0, 2, gray1, dummy, dummy, dummy);

    /* Overwrite with second version */
    hilbert_tables_add(ctx, "overwrite", 0, 2, gray2, dummy, dummy, dummy);

    hilbert_tables_close(ctx);

    /* Verify we get the second version */
    ctx = hilbert_tables_open(TEST_FILE);
    if (!ctx) return 0;

    hilbert_tables_select(ctx, "overwrite", 0);
    uint8_t v = hilbert_gray(ctx, 2, 0);

    hilbert_tables_close(ctx);

    return (v == gray2[0]);
}

/* Test full k=1..7 storage and retrieval with verification */
static int test_full_range(void)
{
    uint8_t gray[128], gray_rank[128], child_entry[128], child_dir[128];
    uint8_t stored_gray[7][128];

    hilbert_tables_ctx_t* ctx = hilbert_tables_create(TEST_FILE);
    if (!ctx) return 0;

    /* Store tables for all k */
    for (int k = 1; k <= 7; k++) {
        generate_random_tables(k, gray, gray_rank, child_entry, child_dir);
        memcpy(stored_gray[k-1], gray, (size_t)(1 << k));

        if (hilbert_tables_add(ctx, "full", 0, k, gray, gray_rank, child_entry, child_dir) < 0) {
            hilbert_tables_close(ctx);
            return 0;
        }
    }

    hilbert_tables_close(ctx);

    /* Verify all k */
    ctx = hilbert_tables_open(TEST_FILE);
    if (!ctx) return 0;

    hilbert_tables_select(ctx, "full", 0);

    for (int k = 1; k <= 7; k++) {
        uint32_t size = 1u << k;
        for (uint32_t w = 0; w < size; w++) {
            uint8_t v = hilbert_gray(ctx, (uint32_t)k, w);
            if (v != stored_gray[k-1][w]) {
                hilbert_tables_close(ctx);
                return 0;
            }
        }
    }

    hilbert_tables_close(ctx);
    return 1;
}

int main(void)
{
    srand((unsigned int)time(NULL));

    printf("Testing HDF5 table storage\n");
    printf("==========================\n");

    TEST(create_close);
    TEST(store_retrieve);
    TEST(multiple_k);
    TEST(count);
    TEST(count_nonexistent);
    TEST(select_invalid);
    TEST(auto_load);
    TEST(overwrite);
    TEST(full_range);

    printf("\n==========================\n");
    printf("Results: %d/%d tests passed\n", tests_passed, tests_run);

    /* Clean up test file */
    remove(TEST_FILE);

    return (tests_passed == tests_run) ? 0 : 1;
}
