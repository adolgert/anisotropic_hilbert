/*
 * range_query_clustering.c
 *
 * Computes range-query clustering statistics for space-filling curves.
 * Measures how many disjoint index intervals a query window produces.
 *
 * Reference: Moon, Jagadish, Faloutsos, Saltz, "Analysis of the Clustering
 * Properties of the Hilbert Space-Filling Curve"
 *
 * ==========================================================================
 * METRIC DEFINITIONS
 * ==========================================================================
 *
 * For a rectangular query window Q placed on a grid mapped by curve C:
 *
 * CLUSTER: A maximal set of grid points inside Q whose curve indices
 *          form a contiguous interval [i, i+1, i+2, ..., j].
 *
 * NUMBER OF CLUSTERS: Count of disjoint index intervals covering all
 *                     points in Q. Equivalently: (number of gaps) + 1,
 *                     where a gap occurs when consecutive sorted indices
 *                     differ by more than 1.
 *
 * INTERPRETATION:
 *   - Each cluster = one contiguous disk read (no seek needed within)
 *   - Fewer clusters = better locality = faster range queries
 *   - Ideal: 1 cluster (all points contiguous along curve)
 *
 * ASYMPTOTIC FORMULA (Theorem 1 from Moon et al.):
 *   For d-dimensional query with total surface area S_q:
 *     E[clusters] = S_q / (2d)
 *
 *   For 2D rectangle with sides a × b:
 *     E[clusters] ≈ (2a + 2b) / 4 = (a + b) / 2
 *
 * BASELINE (from paper):
 *   - 2×2 query: Hilbert = 2.0, Z-curve = 2.625, Gray-coded = 2.5
 *   - Hilbert achieves ~25% fewer clusters than Z-curve
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

/* Forward declarations from hilbert_general.c (linked separately) */
extern uint64_t hilbert_affine_encode_64(const uint32_t *point, const int *m, int n);

/* ========================================================================== */
/* Constants and Configuration                                                */
/* ========================================================================== */

#define CLUSTER_MAX_DIMS 8
#define CLUSTER_MAX_QUERY_AREA (256 * 256)  /* Max supported query window area */

/* ========================================================================== */
/* Index Buffer (for sorting indices within a query window)                   */
/* ========================================================================== */

typedef struct {
    uint64_t *indices;     /* curve indices of points in window */
    int capacity;          /* max query area */
    int count;             /* current count */
} index_buffer_t;

static int index_buffer_alloc(index_buffer_t *buf, int max_area)
{
    if (!buf || max_area <= 0) return -1;
    buf->indices = (uint64_t *)malloc(max_area * sizeof(uint64_t));
    if (!buf->indices) return -1;
    buf->capacity = max_area;
    buf->count = 0;
    return 0;
}

static void index_buffer_free(index_buffer_t *buf)
{
    if (buf && buf->indices) {
        free(buf->indices);
        buf->indices = NULL;
    }
}

/* Comparison function for qsort on uint64_t */
static int compare_uint64(const void *a, const void *b)
{
    uint64_t ua = *(const uint64_t *)a;
    uint64_t ub = *(const uint64_t *)b;
    if (ua < ub) return -1;
    if (ua > ub) return 1;
    return 0;
}

/* ========================================================================== */
/* Index Grid (precomputed curve indices for all grid points)                 */
/* ========================================================================== */

typedef struct {
    uint64_t *indices;     /* index_grid[y * width + x] = curve index at (x, y) */
    int width;             /* grid width */
    int height;            /* grid height */
} index_grid_t;

/*
 * Callback type for encoding a point to a Hilbert index.
 */
typedef uint64_t (*encode_fn_t)(const uint32_t *point, const int *m, int n);

/* Encoder wrappers */
static uint64_t hamilton_encode_wrapper(const uint32_t *point, const int *m, int n)
{
    hamilton_coord_t ham_point[HAMILTON_MAX_DIMS];
    for (int i = 0; i < n; i++) {
        ham_point[i] = point[i];
    }
    return hamilton_encode_64(ham_point, m, n);
}

static uint64_t lc_chi_encode_wrapper(const uint32_t *point, const int *m, int n)
{
    return hilbert_affine_encode_64(point, m, n);
}

/*
 * Build index grid for a 2D domain.
 * Returns 0 on success, -1 on error.
 */
static int index_grid_alloc(index_grid_t *grid, encode_fn_t encode,
                            const int *m, int n)
{
    if (!grid || !encode || !m || n != 2) {
        return -1;
    }

    int width = 1 << m[0];
    int height = 1 << m[1];
    uint64_t total = (uint64_t)width * height;

    grid->indices = (uint64_t *)malloc(total * sizeof(uint64_t));
    if (!grid->indices) return -1;

    grid->width = width;
    grid->height = height;

    /* Encode all points */
    uint32_t point[2];
    for (int y = 0; y < height; y++) {
        point[1] = (uint32_t)y;
        for (int x = 0; x < width; x++) {
            point[0] = (uint32_t)x;
            grid->indices[y * width + x] = encode(point, m, n);
        }
    }

    return 0;
}

static void index_grid_free(index_grid_t *grid)
{
    if (grid && grid->indices) {
        free(grid->indices);
        grid->indices = NULL;
    }
}

/* ========================================================================== */
/* Cluster Counting                                                           */
/* ========================================================================== */

/*
 * Count clusters for a single query window at position (qx, qy).
 *
 * Parameters:
 *   grid         - precomputed index grid
 *   qx, qy       - query window top-left corner
 *   query_width  - query window width
 *   query_height - query window height
 *   buf          - scratch buffer for sorting
 *
 * Returns:
 *   Number of clusters (disjoint index intervals)
 */
static int count_clusters(const index_grid_t *grid,
                          int qx, int qy,
                          int query_width, int query_height,
                          index_buffer_t *buf)
{
    /* Collect indices from query window into buffer */
    buf->count = 0;
    for (int dy = 0; dy < query_height; dy++) {
        for (int dx = 0; dx < query_width; dx++) {
            int x = qx + dx;
            int y = qy + dy;
            buf->indices[buf->count++] = grid->indices[y * grid->width + x];
        }
    }

    /* Sort indices */
    qsort(buf->indices, buf->count, sizeof(uint64_t), compare_uint64);

    /* Count gaps (where index[i] != index[i-1] + 1) */
    int clusters = 1;
    for (int i = 1; i < buf->count; i++) {
        if (buf->indices[i] != buf->indices[i - 1] + 1) {
            clusters++;
        }
    }

    return clusters;
}

/* ========================================================================== */
/* Clustering Statistics                                                      */
/* ========================================================================== */

typedef struct {
    double mean_clusters;
    double p95_clusters;
    int max_clusters;
    int min_clusters;
    uint64_t num_queries;  /* number of window positions tested */
} clustering_stats_t;

/* Comparison function for qsort on int */
static int compare_int(const void *a, const void *b)
{
    int ia = *(const int *)a;
    int ib = *(const int *)b;
    return ia - ib;
}

/*
 * Compute percentile of a sorted array of ints.
 * p should be in [0.0, 1.0].
 */
static double percentile_int(const int *sorted_values, int count, double p)
{
    if (count == 0) return 0.0;
    if (count == 1) return (double)sorted_values[0];

    /* Use linear interpolation for percentile */
    double index = p * (count - 1);
    int lower = (int)index;
    int upper = lower + 1;
    if (upper >= count) upper = count - 1;

    double frac = index - lower;
    return (double)sorted_values[lower] * (1.0 - frac) + (double)sorted_values[upper] * frac;
}

/*
 * Compute statistics over all valid window positions (exhaustive).
 */
static clustering_stats_t compute_clustering_exhaustive(
    const index_grid_t *grid,
    int query_width, int query_height)
{
    clustering_stats_t result = {0.0, 0.0, 0, 0, 0};

    /* Number of valid query positions */
    int n_positions_x = grid->width - query_width + 1;
    int n_positions_y = grid->height - query_height + 1;

    if (n_positions_x <= 0 || n_positions_y <= 0) {
        fprintf(stderr, "ERROR: Query window too large for grid\n");
        return result;
    }

    int n_positions = n_positions_x * n_positions_y;
    result.num_queries = (uint64_t)n_positions;

    /* Allocate array for cluster counts (for percentile computation) */
    int *cluster_counts = (int *)malloc(n_positions * sizeof(int));
    if (!cluster_counts) {
        fprintf(stderr, "ERROR: Failed to allocate cluster_counts array\n");
        return result;
    }

    /* Allocate scratch buffer */
    int query_area = query_width * query_height;
    index_buffer_t buf;
    if (index_buffer_alloc(&buf, query_area) != 0) {
        fprintf(stderr, "ERROR: Failed to allocate index buffer\n");
        free(cluster_counts);
        return result;
    }

    /* Compute cluster counts for all positions */
    int64_t sum_clusters = 0;
    int max_clusters = 0;
    int min_clusters = query_area + 1;  /* Initialize to impossibly high value */
    int idx = 0;

    for (int qy = 0; qy < n_positions_y; qy++) {
        for (int qx = 0; qx < n_positions_x; qx++) {
            int clusters = count_clusters(grid, qx, qy, query_width, query_height, &buf);
            cluster_counts[idx++] = clusters;
            sum_clusters += clusters;
            if (clusters > max_clusters) max_clusters = clusters;
            if (clusters < min_clusters) min_clusters = clusters;
        }
    }

    /* Compute mean */
    result.mean_clusters = (double)sum_clusters / n_positions;
    result.max_clusters = max_clusters;
    result.min_clusters = min_clusters;

    /* Sort for percentile */
    qsort(cluster_counts, n_positions, sizeof(int), compare_int);
    result.p95_clusters = percentile_int(cluster_counts, n_positions, 0.95);

    index_buffer_free(&buf);
    free(cluster_counts);

    return result;
}

/*
 * Simple xorshift64 PRNG for sampling.
 */
static uint64_t xorshift64(uint64_t *state)
{
    uint64_t x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    return x;
}

/*
 * Compute statistics over random window positions (sampled).
 */
static clustering_stats_t compute_clustering_sampled(
    const index_grid_t *grid,
    int query_width, int query_height,
    int num_samples,
    uint64_t seed)
{
    clustering_stats_t result = {0.0, 0.0, 0, 0, 0};

    /* Number of valid query positions */
    int n_positions_x = grid->width - query_width + 1;
    int n_positions_y = grid->height - query_height + 1;

    if (n_positions_x <= 0 || n_positions_y <= 0) {
        fprintf(stderr, "ERROR: Query window too large for grid\n");
        return result;
    }

    result.num_queries = (uint64_t)num_samples;

    /* Allocate array for cluster counts (for percentile computation) */
    int *cluster_counts = (int *)malloc(num_samples * sizeof(int));
    if (!cluster_counts) {
        fprintf(stderr, "ERROR: Failed to allocate cluster_counts array\n");
        return result;
    }

    /* Allocate scratch buffer */
    int query_area = query_width * query_height;
    index_buffer_t buf;
    if (index_buffer_alloc(&buf, query_area) != 0) {
        fprintf(stderr, "ERROR: Failed to allocate index buffer\n");
        free(cluster_counts);
        return result;
    }

    /* Initialize PRNG */
    uint64_t rng_state = seed ? seed : 0xDEADBEEFCAFEBABEULL;

    /* Sample random positions */
    int64_t sum_clusters = 0;
    int max_clusters = 0;
    int min_clusters = query_area + 1;

    for (int i = 0; i < num_samples; i++) {
        int qx = (int)(xorshift64(&rng_state) % (uint64_t)n_positions_x);
        int qy = (int)(xorshift64(&rng_state) % (uint64_t)n_positions_y);

        int clusters = count_clusters(grid, qx, qy, query_width, query_height, &buf);
        cluster_counts[i] = clusters;
        sum_clusters += clusters;
        if (clusters > max_clusters) max_clusters = clusters;
        if (clusters < min_clusters) min_clusters = clusters;
    }

    /* Compute mean */
    result.mean_clusters = (double)sum_clusters / num_samples;
    result.max_clusters = max_clusters;
    result.min_clusters = min_clusters;

    /* Sort for percentile */
    qsort(cluster_counts, num_samples, sizeof(int), compare_int);
    result.p95_clusters = percentile_int(cluster_counts, num_samples, 0.95);

    index_buffer_free(&buf);
    free(cluster_counts);

    return result;
}

/* ========================================================================== */
/* Output Functions                                                           */
/* ========================================================================== */

static void print_clustering_stats(const clustering_stats_t *s, int qw, int qh,
                                   const char *method, const char *label)
{
    fprintf(stderr, "%s (query=%dx%d, method=%s):\n", label, qw, qh, method);
    fprintf(stderr, "  mean_clusters = %.4f\n", s->mean_clusters);
    fprintf(stderr, "  p95_clusters  = %.2f\n", s->p95_clusters);
    fprintf(stderr, "  max_clusters  = %d\n", s->max_clusters);
    fprintf(stderr, "  min_clusters  = %d\n", s->min_clusters);
    fprintf(stderr, "  num_queries   = %llu\n", (unsigned long long)s->num_queries);
}

static void print_csv_header(FILE *fp)
{
    fprintf(fp, "curve,dims,m0,m1,m2,total_points,query_w,query_h,"
            "method,num_queries,mean_clusters,p95_clusters,max_clusters,min_clusters\n");
}

static void print_csv_row(FILE *fp, const char *curve_name, const int *m, int n,
                          uint64_t n_points, int query_w, int query_h,
                          const char *method, const clustering_stats_t *stats)
{
    fprintf(fp, "%s,%d,%d,%d,%d,%llu,%d,%d,%s,%llu,%.6f,%.2f,%d,%d\n",
            curve_name, n,
            m[0], (n > 1) ? m[1] : 0, (n > 2) ? m[2] : 0,
            (unsigned long long)n_points, query_w, query_h,
            method, (unsigned long long)stats->num_queries,
            stats->mean_clusters, stats->p95_clusters,
            stats->max_clusters, stats->min_clusters);
}

/* ========================================================================== */
/* Main Driver                                                                */
/* ========================================================================== */

typedef struct {
    const char *name;
    int m[3];
    int n;
} domain_config_t;

/* Domain configurations matching Table 3/4 in the plan (262K points) */
static const domain_config_t domains[] = {
    {"D0_512x512",    {9, 9, 0}, 2},   /* 262,144 points, aspect 1:1 */
    {"D1_2048x128",   {11, 7, 0}, 2},  /* 262,144 points, aspect 16:1 */
    {"D2_4096x64",    {12, 6, 0}, 2},  /* 262,144 points, aspect 64:1 */
    {"D3_8192x32",    {13, 5, 0}, 2},  /* 262,144 points, aspect 256:1 */
};

#define N_DOMAINS (sizeof(domains) / sizeof(domains[0]))

typedef struct {
    int width;
    int height;
} query_size_t;

/* Query window sizes to test */
static const query_size_t query_sizes[] = {
    {4, 4},     /* perimeter 16, ~4 expected clusters */
    {8, 8},     /* perimeter 32, ~8 expected clusters */
    {16, 16},   /* perimeter 64, ~16 expected clusters */
    {64, 4},    /* perimeter 136, ~34 expected clusters - anisotropic */
    {4, 64},    /* perimeter 136, ~34 expected clusters - anisotropic (rotated) */
    {32, 32},   /* perimeter 128, ~32 expected clusters */
};

#define N_QUERY_SIZES (sizeof(query_sizes) / sizeof(query_sizes[0]))

/* Thresholds for exhaustive vs sampled computation */
#define EXHAUSTIVE_THRESHOLD (512 * 512)  /* Max query positions for exhaustive */
#define SAMPLE_SIZE 10000                 /* Number of samples for sampled method */
#define SAMPLE_SEED 42                    /* Random seed for reproducibility */

static const char *HDF5_FILE = "hilbert_tables.h5";

static void run_query_size(FILE *csv_fp, const char *curve_name,
                           const index_grid_t *grid, const int *m, int n,
                           uint64_t n_points, int qw, int qh)
{
    /* Check if query fits in grid */
    if (qw > grid->width || qh > grid->height) {
        fprintf(stderr, "  Skipping query %dx%d (larger than grid)\n", qw, qh);
        return;
    }

    /* Determine method based on number of positions */
    int n_positions_x = grid->width - qw + 1;
    int n_positions_y = grid->height - qh + 1;
    int n_positions = n_positions_x * n_positions_y;

    const char *method;
    clustering_stats_t stats;

    if (n_positions <= EXHAUSTIVE_THRESHOLD) {
        method = "exhaustive";
        stats = compute_clustering_exhaustive(grid, qw, qh);
    } else {
        method = "sampled";
        stats = compute_clustering_sampled(grid, qw, qh, SAMPLE_SIZE, SAMPLE_SEED);
    }

    print_clustering_stats(&stats, qw, qh, method, curve_name);
    print_csv_row(csv_fp, curve_name, m, n, n_points, qw, qh, method, &stats);
}

static void run_curve_variant(FILE *csv_fp, const char *curve_name,
                              const index_grid_t *grid, const int *m, int n)
{
    uint64_t n_points = (uint64_t)grid->width * grid->height;

    for (size_t qs = 0; qs < N_QUERY_SIZES; qs++) {
        int qw = query_sizes[qs].width;
        int qh = query_sizes[qs].height;
        run_query_size(csv_fp, curve_name, grid, m, n, n_points, qw, qh);
    }
}

static void run_domain(FILE *csv_fp, const domain_config_t *domain)
{
    int m_array[CLUSTER_MAX_DIMS] = {0};
    for (int i = 0; i < domain->n; i++) {
        m_array[i] = domain->m[i];
    }

    fprintf(stderr, "\n=== Domain: %s (dims=%d, m={%d,%d,%d}) ===\n",
            domain->name, domain->n, m_array[0], m_array[1], m_array[2]);

    /* Hamilton-CHI */
    {
        fprintf(stderr, "Computing Hamilton-CHI...\n");
        index_grid_t grid = {0};
        if (index_grid_alloc(&grid, hamilton_encode_wrapper, m_array, domain->n) != 0) {
            fprintf(stderr, "  ERROR: Failed to allocate index grid\n");
            return;
        }

        run_curve_variant(csv_fp, "Hamilton-CHI", &grid, m_array, domain->n);
        index_grid_free(&grid);
    }

    /* LC-CHI-BRGC */
    {
        fprintf(stderr, "Computing LC-CHI-BRGC...\n");
        if (hilbert_tables_init(HDF5_FILE, "brgc", 0) != 0) {
            fprintf(stderr, "  ERROR: Failed to load BRGC tables from %s\n", HDF5_FILE);
        } else {
            index_grid_t grid = {0};
            if (index_grid_alloc(&grid, lc_chi_encode_wrapper, m_array, domain->n) != 0) {
                fprintf(stderr, "  ERROR: Failed to allocate index grid\n");
            } else {
                run_curve_variant(csv_fp, "LC-CHI-BRGC", &grid, m_array, domain->n);
                index_grid_free(&grid);
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
            index_grid_t grid = {0};
            if (index_grid_alloc(&grid, lc_chi_encode_wrapper, m_array, domain->n) != 0) {
                fprintf(stderr, "  ERROR: Failed to allocate index grid\n");
            } else {
                run_curve_variant(csv_fp, "LC-CHI-Balanced", &grid, m_array, domain->n);
                index_grid_free(&grid);
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
            index_grid_t grid = {0};
            if (index_grid_alloc(&grid, lc_chi_encode_wrapper, m_array, domain->n) != 0) {
                fprintf(stderr, "  ERROR: Failed to allocate index grid\n");
            } else {
                run_curve_variant(csv_fp, "LC-CHI-Random", &grid, m_array, domain->n);
                index_grid_free(&grid);
            }
            hilbert_tables_cleanup();
        }
    }
}

static void print_usage(const char *prog)
{
    fprintf(stderr, "Usage: %s [OPTIONS]\n", prog);
    fprintf(stderr, "\nComputes range-query clustering statistics for space-filling curves.\n");
    fprintf(stderr, "Measures how many disjoint index intervals a query window produces.\n");
    fprintf(stderr, "\nOptions:\n");
    fprintf(stderr, "  --output FILE    Write CSV to FILE (default: stdout)\n");
    fprintf(stderr, "  --hdf5 FILE      Use FILE for Hilbert tables (default: hilbert_tables.h5)\n");
    fprintf(stderr, "  --help           Show this help\n");
    fprintf(stderr, "\nQuery sizes tested:\n");
    for (size_t i = 0; i < N_QUERY_SIZES; i++) {
        int qw = query_sizes[i].width;
        int qh = query_sizes[i].height;
        int perimeter = 2 * (qw + qh);
        fprintf(stderr, "  %dx%d (perimeter=%d, expected clusters ~%.1f)\n",
                qw, qh, perimeter, (double)perimeter / 4.0);
    }
    fprintf(stderr, "\nDomain configurations:\n");
    for (size_t i = 0; i < N_DOMAINS; i++) {
        fprintf(stderr, "  %s: m=(%d,%d) -> %llu points\n",
                domains[i].name, domains[i].m[0], domains[i].m[1],
                (unsigned long long)((uint64_t)1 << (domains[i].m[0] + domains[i].m[1])));
    }
    fprintf(stderr, "\nMethod selection:\n");
    fprintf(stderr, "  - Exhaustive: when positions <= %d\n", EXHAUSTIVE_THRESHOLD);
    fprintf(stderr, "  - Sampled (%d queries): when positions > %d\n",
            SAMPLE_SIZE, EXHAUSTIVE_THRESHOLD);
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
    print_csv_header(csv_fp);

    /* Run all domains */
    fprintf(stderr, "\n========================================\n");
    fprintf(stderr, "Range-Query Clustering Statistics\n");
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
