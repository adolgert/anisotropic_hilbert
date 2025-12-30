/*
 * bounding_box_stats.c
 *
 * Computes practical block bounding-box statistics for R-tree indexing.
 * Simulates packing consecutive curve points into blocks of size B.
 *
 * Reference: Haverkort & van Walderveen (2010), Section 3.4
 *
 * ==========================================================================
 * METRIC DEFINITIONS
 * ==========================================================================
 *
 * Given a space-filling curve on N points, partition into blocks of B
 * consecutive points (last block may be smaller).
 *
 * For each block:
 *   bbox_area = product over dimensions of (max_coord - min_coord + 1)
 *   bbox_perimeter = 2 * sum over dimensions of (max_coord - min_coord + 1)
 *
 * Report:
 *   mean_area_ratio = mean(bbox_area / B) over all blocks
 *   p95_area_ratio = 95th percentile of (bbox_area / B)
 *   max_area_ratio = max(bbox_area / B)
 *   max_peri_ratio = max(bbox_perimeter / sqrt(B))
 *
 * Ideal values: area_ratio = 1 (perfect packing), but impossible.
 * For Hilbert on squares: mean ~ 1.44 (from Haverkort Table 1 ABA)
 *
 * ==========================================================================
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <assert.h>

/* Hamilton implementation header */
#include "hamilton.h"

/* LC-CHI implementation (table-based) */
#include "setup_hilbert.h"

/* Forward declaration from hilbert_general.c (linked separately) */
extern void hilbert_affine_decode_64(uint64_t h, const int *m, int n, uint32_t *point);

/* ========================================================================== */
/* Curve Point Storage (self-contained implementation)                        */
/* ========================================================================== */

#define BBOX_MAX_DIMS 8

/*
 * Callback type for decoding a Hilbert index to a point.
 */
typedef void (*bbox_decode_fn_t)(uint64_t h, const int *m, int n, uint32_t *point);

/*
 * Precomputed curve representation: all points decoded and stored.
 */
typedef struct {
    uint32_t *points;              /* Array of N * n_dims coordinates */
    uint64_t n_points;             /* Total number of points */
    int n_dims;                    /* Number of dimensions */
    int m[BBOX_MAX_DIMS];          /* Bits per axis */
} bbox_curve_points_t;

/*
 * Get pointer to coordinates of point at index h.
 */
static inline const uint32_t *bbox_curve_point_at(const bbox_curve_points_t *c, uint64_t h)
{
    return c->points + h * (uint64_t)c->n_dims;
}

/*
 * Precompute all points along the curve.
 * Caller must free points->points when done.
 *
 * Returns 0 on success, -1 on error.
 */
static int bbox_curve_points_alloc(bbox_curve_points_t *c, bbox_decode_fn_t decode,
                                   const int *m, int n)
{
    if (!c || !decode || !m || n <= 0 || n > BBOX_MAX_DIMS) {
        return -1;
    }

    int total_bits = 0;
    for (int i = 0; i < n; i++) {
        if (m[i] < 0 || m[i] > 32) return -1;
        c->m[i] = m[i];
        total_bits += m[i];
    }
    if (total_bits > 63) {
        /* Too many points for 64-bit indexing */
        return -1;
    }

    c->n_dims = n;
    c->n_points = (uint64_t)1 << total_bits;

    /* Allocate point storage */
    c->points = (uint32_t *)malloc(c->n_points * (uint64_t)n * sizeof(uint32_t));
    if (!c->points) {
        return -1;
    }

    /* Decode all points */
    for (uint64_t h = 0; h < c->n_points; h++) {
        decode(h, m, n, c->points + h * (uint64_t)n);
    }

    return 0;
}

/*
 * Free memory allocated by bbox_curve_points_alloc.
 */
static void bbox_curve_points_free(bbox_curve_points_t *c)
{
    if (c && c->points) {
        free(c->points);
        c->points = NULL;
    }
}

/* ========================================================================== */
/* Decoder Wrappers                                                           */
/* ========================================================================== */

static void hamilton_decode_wrapper(uint64_t h, const int *m, int n, uint32_t *point)
{
    hamilton_coord_t ham_point[HAMILTON_MAX_DIMS];
    hamilton_decode_64(h, m, n, ham_point);
    for (int i = 0; i < n; i++) {
        point[i] = ham_point[i];
    }
}

static void lc_chi_decode_wrapper(uint64_t h, const int *m, int n, uint32_t *point)
{
    hilbert_affine_decode_64(h, m, n, point);
}

/* ========================================================================== */
/* Block Bounding Box Statistics                                              */
/* ========================================================================== */

typedef struct {
    double mean_area_ratio;   /* mean(bbox_area / B) */
    double p95_area_ratio;    /* 95th percentile of (bbox_area / B) */
    double max_area_ratio;    /* max(bbox_area / B) */
    double max_peri_ratio;    /* max(bbox_perimeter / sqrt(B)) */
} block_bbox_stats_t;

/* Comparison function for qsort on doubles */
static int compare_double(const void *a, const void *b)
{
    double da = *(const double *)a;
    double db = *(const double *)b;
    if (da < db) return -1;
    if (da > db) return 1;
    return 0;
}

/*
 * Compute percentile of a sorted array of doubles.
 * p should be in [0.0, 1.0].
 */
static double percentile(const double *sorted_values, int count, double p)
{
    if (count == 0) return 0.0;
    if (count == 1) return sorted_values[0];

    /* Use linear interpolation for percentile */
    double index = p * (count - 1);
    int lower = (int)index;
    int upper = lower + 1;
    if (upper >= count) upper = count - 1;

    double frac = index - lower;
    return sorted_values[lower] * (1.0 - frac) + sorted_values[upper] * frac;
}

/*
 * Compute block bounding-box statistics for the given curve.
 *
 * Parameters:
 *   curve       - precomputed curve points
 *   block_size  - number of points per block (B)
 *
 * Returns:
 *   block_bbox_stats_t with computed statistics
 */
static block_bbox_stats_t compute_block_stats(const bbox_curve_points_t *curve, int block_size)
{
    block_bbox_stats_t result = {0.0, 0.0, 0.0, 0.0};

    uint64_t N = curve->n_points;
    int n_dims = curve->n_dims;
    int B = block_size;

    /* Number of full blocks, plus possibly one partial block */
    int n_blocks = (int)((N + B - 1) / B);

    if (n_blocks == 0) return result;

    /* Allocate array for area ratios (for percentile computation) */
    double *area_ratios = (double *)malloc(n_blocks * sizeof(double));
    if (!area_ratios) {
        fprintf(stderr, "ERROR: Failed to allocate area_ratios array\n");
        return result;
    }

    double sum_area_ratio = 0.0;
    double max_area_ratio = 0.0;
    double max_peri_ratio = 0.0;

    for (int blk = 0; blk < n_blocks; blk++) {
        uint64_t start = (uint64_t)blk * B;
        uint64_t end = start + B;
        if (end > N) end = N;

        /* Initialize bounding box with first point in block */
        const uint32_t *p0 = bbox_curve_point_at(curve, start);
        uint32_t bbox_min[BBOX_MAX_DIMS];
        uint32_t bbox_max[BBOX_MAX_DIMS];

        for (int d = 0; d < n_dims; d++) {
            bbox_min[d] = p0[d];
            bbox_max[d] = p0[d];
        }

        /* Expand bounding box to include all points in block */
        for (uint64_t h = start + 1; h < end; h++) {
            const uint32_t *p = bbox_curve_point_at(curve, h);
            for (int d = 0; d < n_dims; d++) {
                if (p[d] < bbox_min[d]) bbox_min[d] = p[d];
                if (p[d] > bbox_max[d]) bbox_max[d] = p[d];
            }
        }

        /* Compute bbox area (volume) and perimeter */
        uint64_t bbox_area = 1;
        uint64_t perimeter_sum = 0;  /* Sum of side lengths */

        for (int d = 0; d < n_dims; d++) {
            uint32_t side = bbox_max[d] - bbox_min[d] + 1;
            bbox_area *= side;
            perimeter_sum += side;
        }

        /* Compute ratios */
        double area_ratio = (double)bbox_area / (double)B;
        double full_perimeter = 2.0 * (double)perimeter_sum;
        double peri_ratio = full_perimeter / sqrt((double)B);

        /* Accumulate statistics */
        area_ratios[blk] = area_ratio;
        sum_area_ratio += area_ratio;

        if (area_ratio > max_area_ratio) max_area_ratio = area_ratio;
        if (peri_ratio > max_peri_ratio) max_peri_ratio = peri_ratio;
    }

    /* Compute mean area ratio */
    result.mean_area_ratio = sum_area_ratio / n_blocks;
    result.max_area_ratio = max_area_ratio;
    result.max_peri_ratio = max_peri_ratio;

    /* Sort area_ratios for percentile computation */
    qsort(area_ratios, n_blocks, sizeof(double), compare_double);
    result.p95_area_ratio = percentile(area_ratios, n_blocks, 0.95);

    free(area_ratios);

    return result;
}

/* ========================================================================== */
/* Output Functions                                                           */
/* ========================================================================== */

static void print_block_stats(const block_bbox_stats_t *s, int block_size, const char *label)
{
    fprintf(stderr, "%s (B=%d):\n", label, block_size);
    fprintf(stderr, "  mean_area_ratio = %.4f\n", s->mean_area_ratio);
    fprintf(stderr, "  p95_area_ratio  = %.4f\n", s->p95_area_ratio);
    fprintf(stderr, "  max_area_ratio  = %.4f\n", s->max_area_ratio);
    fprintf(stderr, "  max_peri_ratio  = %.4f\n", s->max_peri_ratio);
}

static void print_csv_header_bbox(FILE *fp)
{
    fprintf(fp, "curve,dims,m0,m1,m2,total_points,block_size,"
            "mean_area_ratio,p95_area_ratio,max_area_ratio,max_peri_ratio\n");
}

static void print_csv_row_bbox(FILE *fp, const char *curve_name, const int *m, int n,
                               uint64_t n_points, int block_size,
                               const block_bbox_stats_t *stats)
{
    fprintf(fp, "%s,%d,%d,%d,%d,%llu,%d,%.6f,%.6f,%.6f,%.6f\n",
            curve_name, n,
            m[0], (n > 1) ? m[1] : 0, (n > 2) ? m[2] : 0,
            (unsigned long long)n_points, block_size,
            stats->mean_area_ratio, stats->p95_area_ratio,
            stats->max_area_ratio, stats->max_peri_ratio);
}

/* ========================================================================== */
/* Main Driver                                                                */
/* ========================================================================== */

typedef struct {
    const char *name;
    int m[3];
    int n;
} domain_config_t;

/* Domain configurations matching Table 3/4 in the plan */
static const domain_config_t domains[] = {
    {"D0_512x512",    {9, 9, 0}, 2},   /* 262,144 points, aspect 1:1 */
    {"D1_2048x128",   {11, 7, 0}, 2},  /* 262,144 points, aspect 16:1 */
    {"D2_4096x64",    {12, 6, 0}, 2},  /* 262,144 points, aspect 64:1 */
    {"D3_8192x32",    {13, 5, 0}, 2},  /* 262,144 points, aspect 256:1 */
};

#define N_DOMAINS (sizeof(domains) / sizeof(domains[0]))

/* Block sizes to test:
 * - Power-of-2 sizes: align with Hilbert recursive structure
 * - Non-power-of-2 sizes: straddle recursive boundaries, reveal discontinuities
 */
static const int block_sizes[] = {32, 33, 64, 100, 128, 256, 500, 512, 1024};
#define N_BLOCK_SIZES (sizeof(block_sizes) / sizeof(block_sizes[0]))

static const char *HDF5_FILE = "hilbert_tables.h5";

static void run_curve_variant(FILE *csv_fp, const char *curve_name,
                              const bbox_curve_points_t *curve, const int *m, int n)
{
    for (size_t bs = 0; bs < N_BLOCK_SIZES; bs++) {
        int B = block_sizes[bs];

        block_bbox_stats_t stats = compute_block_stats(curve, B);
        print_block_stats(&stats, B, curve_name);
        print_csv_row_bbox(csv_fp, curve_name, m, n, curve->n_points, B, &stats);
    }
}

static void run_domain(FILE *csv_fp, const domain_config_t *domain)
{
    int m_array[BBOX_MAX_DIMS] = {0};
    for (int i = 0; i < domain->n; i++) {
        m_array[i] = domain->m[i];
    }

    fprintf(stderr, "\n=== Domain: %s (dims=%d, m={%d,%d,%d}) ===\n",
            domain->name, domain->n, m_array[0], m_array[1], m_array[2]);

    /* Hamilton-CHI */
    {
        fprintf(stderr, "Computing Hamilton-CHI...\n");
        bbox_curve_points_t curve = {0};
        if (bbox_curve_points_alloc(&curve, hamilton_decode_wrapper, m_array, domain->n) != 0) {
            fprintf(stderr, "  ERROR: Failed to allocate curve points\n");
            return;
        }

        run_curve_variant(csv_fp, "Hamilton-CHI", &curve, m_array, domain->n);
        bbox_curve_points_free(&curve);
    }

    /* LC-CHI-BRGC */
    {
        fprintf(stderr, "Computing LC-CHI-BRGC...\n");
        if (hilbert_tables_init(HDF5_FILE, "brgc", 0) != 0) {
            fprintf(stderr, "  ERROR: Failed to load BRGC tables from %s\n", HDF5_FILE);
        } else {
            bbox_curve_points_t curve = {0};
            if (bbox_curve_points_alloc(&curve, lc_chi_decode_wrapper, m_array, domain->n) != 0) {
                fprintf(stderr, "  ERROR: Failed to allocate curve points\n");
            } else {
                run_curve_variant(csv_fp, "LC-CHI-BRGC", &curve, m_array, domain->n);
                bbox_curve_points_free(&curve);
            }
            hilbert_tables_cleanup();
        }
    }

    /* LC-CHI-Balanced (if tables exist) */
    {
        fprintf(stderr, "Computing LC-CHI-Balanced...\n");
        if (hilbert_tables_init(HDF5_FILE, "balanced", 0) != 0) {
            fprintf(stderr, "  SKIPPED: No balanced tables in %s\n", HDF5_FILE);
        } else {
            bbox_curve_points_t curve = {0};
            if (bbox_curve_points_alloc(&curve, lc_chi_decode_wrapper, m_array, domain->n) != 0) {
                fprintf(stderr, "  ERROR: Failed to allocate curve points\n");
            } else {
                run_curve_variant(csv_fp, "LC-CHI-Balanced", &curve, m_array, domain->n);
                bbox_curve_points_free(&curve);
            }
            hilbert_tables_cleanup();
        }
    }

    /* LC-CHI-Random (if tables exist) */
    {
        fprintf(stderr, "Computing LC-CHI-Random...\n");
        if (hilbert_tables_init(HDF5_FILE, "random", 0) != 0) {
            fprintf(stderr, "  SKIPPED: No random tables in %s\n", HDF5_FILE);
        } else {
            bbox_curve_points_t curve = {0};
            if (bbox_curve_points_alloc(&curve, lc_chi_decode_wrapper, m_array, domain->n) != 0) {
                fprintf(stderr, "  ERROR: Failed to allocate curve points\n");
            } else {
                run_curve_variant(csv_fp, "LC-CHI-Random", &curve, m_array, domain->n);
                bbox_curve_points_free(&curve);
            }
            hilbert_tables_cleanup();
        }
    }
}

static void print_usage(const char *prog)
{
    fprintf(stderr, "Usage: %s [OPTIONS]\n", prog);
    fprintf(stderr, "\nComputes R-tree block bounding-box statistics for space-filling curves.\n");
    fprintf(stderr, "\nOptions:\n");
    fprintf(stderr, "  --output FILE    Write CSV to FILE (default: stdout)\n");
    fprintf(stderr, "  --hdf5 FILE      Use FILE for Hilbert tables (default: hilbert_tables.h5)\n");
    fprintf(stderr, "  --help           Show this help\n");
    fprintf(stderr, "\nBlock sizes tested: 32, 33, 64, 100, 128, 256, 500, 512, 1024\n");
    fprintf(stderr, "Domain configurations:\n");
    for (size_t i = 0; i < N_DOMAINS; i++) {
        fprintf(stderr, "  %s: m=(%d,%d) -> %llu points\n",
                domains[i].name, domains[i].m[0], domains[i].m[1],
                (unsigned long long)((uint64_t)1 << (domains[i].m[0] + domains[i].m[1])));
    }
}

int main(int argc, char **argv)
{
    const char *output_file = NULL;
    const char *hdf5_file = HDF5_FILE;

    /* Parse arguments */
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--output") == 0 && i + 1 < argc) {
            output_file = argv[++i];
        } else if (strcmp(argv[i], "--hdf5") == 0 && i + 1 < argc) {
            hdf5_file = argv[++i];
        } else if (strcmp(argv[i], "--help") == 0) {
            print_usage(argv[0]);
            return 0;
        } else {
            fprintf(stderr, "Unknown option: %s\n", argv[i]);
            print_usage(argv[0]);
            return 1;
        }
    }

    /* Note about HDF5 file */
    if (strcmp(hdf5_file, HDF5_FILE) != 0) {
        fprintf(stderr, "Note: HDF5 file override not yet implemented, using: %s\n", HDF5_FILE);
    }

    /* Open output file */
    FILE *csv_fp = stdout;
    if (output_file) {
        csv_fp = fopen(output_file, "w");
        if (!csv_fp) {
            fprintf(stderr, "ERROR: Cannot open output file: %s\n", output_file);
            return 1;
        }
    }

    /* Print header */
    print_csv_header_bbox(csv_fp);

    /* Run all domains */
    fprintf(stderr, "\n========================================\n");
    fprintf(stderr, "Block Bounding-Box Statistics\n");
    fprintf(stderr, "========================================\n");

    for (size_t i = 0; i < N_DOMAINS; i++) {
        run_domain(csv_fp, &domains[i]);
    }

    fprintf(stderr, "\nDone.\n");

    if (output_file) {
        fclose(csv_fp);
        fprintf(stderr, "Results written to: %s\n", output_file);
    }

    return 0;
}
