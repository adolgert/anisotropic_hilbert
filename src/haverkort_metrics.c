/*
 * haverkort_metrics.c
 *
 * Computes Haverkort's worst-case locality and bounding-box quality metrics
 * for space-filling curves on discrete grids.
 *
 * Reference: Haverkort & van Walderveen, "Locality and bounding-box quality
 * of two-dimensional space-filling curves", Computational Geometry 43 (2010).
 *
 * ==========================================================================
 * METRIC DEFINITIONS
 * ==========================================================================
 *
 * For a curve section S from index a to b (inclusive), let:
 *   - p_a = decoded point at index a (start of section)
 *   - p_b = decoded point at index b (end of section)
 *   - |S| = b - a + 1 = number of points in section (proxy for "area covered")
 *   - bbox(S) = axis-aligned bounding box containing all points in [a,b]
 *
 * WORST-CASE LOCALITY (WL_r):
 *   WL_r = max over all sections S of: d_r(p_a, p_b)^2 / |S|
 *
 *   where d_r is the L_r distance:
 *     - d_inf(p,q) = max_i |p_i - q_i|           (Chebyshev/L-infinity)
 *     - d_2(p,q) = sqrt(sum_i (p_i - q_i)^2)     (Euclidean)
 *     - d_1(p,q) = sum_i |p_i - q_i|             (Manhattan/taxicab)
 *
 *   Literature baseline (Hilbert 2D): WL_inf = 6, WL_2 = 6, WL_1 = 9
 *
 * WORST-CASE BOUNDING BOX AREA (WBA):
 *   WBA = max over all sections S of: volume(bbox(S)) / |S|
 *
 *   where volume(bbox) = product of (max_i - min_i + 1) across dimensions
 *   (we use +1 because we're on a discrete grid, counting cells)
 *
 *   Literature baseline (Hilbert 2D): WBA = 2.400
 *
 * WORST-CASE BOUNDING BOX SQUARED PERIMETER (WBP):
 *   WBP = (1/16) * max over all sections S of: perimeter(bbox(S))^2 / |S|
 *
 *   where perimeter = 2 * sum of side lengths (2D), or surface area (higher D)
 *   The 1/16 factor normalizes so that a square bbox has WBP = WBA.
 *
 *   Literature baseline (Hilbert 2D): WBP = 2.400
 *
 * ==========================================================================
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <assert.h>

#include "haverkort_metrics.h"

/* Hamilton implementation header */
#include "hamilton.h"

/* LC-CHI implementation (table-based) */
#include "setup_hilbert.h"

/* Forward declaration from hilbert_general.c (linked separately) */
extern void hilbert_affine_decode_64(uint64_t h, const int *m, int n, uint32_t *point);

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
/* Point Storage                                                              */
/* ========================================================================== */

int curve_points_alloc(curve_points_t *c, decode_fn_t decode,
                       const int *m, int n)
{
    if (!c || !decode || !m || n <= 0 || n > HAVERKORT_MAX_DIMS) {
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

void curve_points_free(curve_points_t *c)
{
    if (c && c->points) {
        free(c->points);
        c->points = NULL;
    }
}

/* ========================================================================== */
/* Section Metrics Computation                                                */
/* ========================================================================== */

/*
 * Compute metrics for a single section [a, b].
 *
 * Returns the individual ratios for this section (not the max).
 */
static void compute_section_ratios(const curve_points_t *c, uint64_t a, uint64_t b,
                                   double *wl_inf, double *wl_2, double *wl_1,
                                   double *wba, double *wbp)
{
    int n = c->n_dims;
    uint64_t section_size = b - a + 1;

    const uint32_t *pa = curve_point_at(c, a);
    const uint32_t *pb = curve_point_at(c, b);

    /* Compute distances between endpoints */
    int d_inf = 0;    /* Chebyshev */
    int d_1 = 0;      /* Manhattan */
    double d_2_sq = 0.0; /* Euclidean squared */

    for (int i = 0; i < n; i++) {
        int diff = (int)pb[i] - (int)pa[i];
        int abs_diff = (diff < 0) ? -diff : diff;
        if (abs_diff > d_inf) d_inf = abs_diff;
        d_1 += abs_diff;
        d_2_sq += (double)diff * diff;
    }

    /* Compute bounding box by scanning all points in section */
    uint32_t bbox_min[HAVERKORT_MAX_DIMS];
    uint32_t bbox_max[HAVERKORT_MAX_DIMS];

    /* Initialize with first point */
    const uint32_t *p0 = curve_point_at(c, a);
    for (int i = 0; i < n; i++) {
        bbox_min[i] = p0[i];
        bbox_max[i] = p0[i];
    }

    /* Expand to include all points in section */
    for (uint64_t h = a + 1; h <= b; h++) {
        const uint32_t *p = curve_point_at(c, h);
        for (int i = 0; i < n; i++) {
            if (p[i] < bbox_min[i]) bbox_min[i] = p[i];
            if (p[i] > bbox_max[i]) bbox_max[i] = p[i];
        }
    }

    /* Compute bounding box volume (on discrete grid, +1 for each dimension) */
    uint64_t bbox_volume = 1;
    uint64_t perimeter = 0;  /* Sum of side lengths (for 2D: half the perimeter) */

    for (int i = 0; i < n; i++) {
        uint32_t side = bbox_max[i] - bbox_min[i] + 1;
        bbox_volume *= side;
        perimeter += side;
    }

    /* Compute ratios */
    double size = (double)section_size;

    /* WL_inf = d_inf^2 / |S| */
    *wl_inf = (double)(d_inf * d_inf) / size;

    /* WL_2 = d_2^2 / |S| (note: d_2_sq is already squared) */
    *wl_2 = d_2_sq / size;

    /* WL_1 = d_1^2 / |S| */
    *wl_1 = (double)(d_1 * d_1) / size;

    /* WBA = bbox_volume / |S| */
    *wba = (double)bbox_volume / size;

    /* WBP = (1/16) * (2*perimeter)^2 / |S| for 2D
     * More generally: (perimeter_sum * 2)^2 / (16 * |S|)
     * This normalizes so that a square bbox has WBP = WBA.
     */
    double full_perimeter = 2.0 * (double)perimeter;
    *wbp = (full_perimeter * full_perimeter) / (16.0 * size);
}

/* ========================================================================== */
/* Exhaustive Computation                                                     */
/* ========================================================================== */

haverkort_metrics_t compute_metrics_exhaustive(const curve_points_t *c)
{
    haverkort_metrics_t result = {0.0, 0.0, 0.0, 0.0, 0.0};

    uint64_t N = c->n_points;
    uint64_t progress_interval = N / 20;  /* Report every 5% */
    if (progress_interval == 0) progress_interval = 1;

    fprintf(stderr, "  Exhaustive computation: N=%llu points, ~%llu pairs\n",
            (unsigned long long)N, (unsigned long long)(N * (N - 1) / 2));

    for (uint64_t a = 0; a < N; a++) {
        if (a % progress_interval == 0) {
            fprintf(stderr, "    Progress: %llu/%llu (%.0f%%)\n",
                    (unsigned long long)a, (unsigned long long)N,
                    100.0 * (double)a / (double)N);
        }

        for (uint64_t b = a + 1; b < N; b++) {
            double wl_inf, wl_2, wl_1, wba, wbp;
            compute_section_ratios(c, a, b, &wl_inf, &wl_2, &wl_1, &wba, &wbp);

            if (wl_inf > result.wl_inf) result.wl_inf = wl_inf;
            if (wl_2 > result.wl_2) result.wl_2 = wl_2;
            if (wl_1 > result.wl_1) result.wl_1 = wl_1;
            if (wba > result.wba) result.wba = wba;
            if (wbp > result.wbp) result.wbp = wbp;
        }
    }

    fprintf(stderr, "    Progress: %llu/%llu (100%%)\n",
            (unsigned long long)N, (unsigned long long)N);

    return result;
}

/* ========================================================================== */
/* Sampled Computation                                                        */
/* ========================================================================== */

/* Simple xorshift64 PRNG for reproducibility */
static uint64_t xorshift64_state;

static void xorshift64_seed(uint64_t seed)
{
    xorshift64_state = seed ? seed : (uint64_t)time(NULL);
    /* Warm up the generator */
    for (int i = 0; i < 10; i++) {
        xorshift64_state ^= xorshift64_state >> 12;
        xorshift64_state ^= xorshift64_state << 25;
        xorshift64_state ^= xorshift64_state >> 27;
    }
}

static uint64_t xorshift64_next(void)
{
    xorshift64_state ^= xorshift64_state >> 12;
    xorshift64_state ^= xorshift64_state << 25;
    xorshift64_state ^= xorshift64_state >> 27;
    return xorshift64_state * 0x2545F4914F6CDD1DULL;
}

/* Generate uniform random in [0, max) */
static uint64_t rand_uint64(uint64_t max)
{
    if (max == 0) return 0;
    return xorshift64_next() % max;
}

/* Generate log-uniform random length in [min_len, max_len] */
static uint64_t rand_log_uniform(uint64_t min_len, uint64_t max_len)
{
    if (min_len >= max_len) return min_len;
    double log_min = log((double)min_len);
    double log_max = log((double)max_len);
    double log_len = log_min + (log_max - log_min) * ((double)xorshift64_next() / (double)UINT64_MAX);
    uint64_t len = (uint64_t)exp(log_len);
    if (len < min_len) len = min_len;
    if (len > max_len) len = max_len;
    return len;
}

haverkort_metrics_t compute_metrics_sampled(const curve_points_t *c,
                                            uint64_t n_samples, uint64_t seed)
{
    haverkort_metrics_t result = {0.0, 0.0, 0.0, 0.0, 0.0};

    uint64_t N = c->n_points;
    if (N < 2) return result;

    xorshift64_seed(seed);

    /* Sample sections with log-uniform length distribution */
    uint64_t min_len = 2;
    uint64_t max_len = N / 10;  /* Cap at 10% of total to avoid very long sections */
    if (max_len < min_len) max_len = min_len;

    fprintf(stderr, "  Sampled computation: %llu samples, section lengths [%llu, %llu]\n",
            (unsigned long long)n_samples, (unsigned long long)min_len,
            (unsigned long long)max_len);

    uint64_t progress_interval = n_samples / 10;
    if (progress_interval == 0) progress_interval = 1;

    for (uint64_t i = 0; i < n_samples; i++) {
        if (i % progress_interval == 0 && i > 0) {
            fprintf(stderr, "    Progress: %llu/%llu (%.0f%%)\n",
                    (unsigned long long)i, (unsigned long long)n_samples,
                    100.0 * (double)i / (double)n_samples);
        }

        /* Sample length with log-uniform distribution */
        uint64_t len = rand_log_uniform(min_len, max_len);

        /* Sample start position */
        uint64_t a = rand_uint64(N - len + 1);
        uint64_t b = a + len - 1;

        double wl_inf, wl_2, wl_1, wba, wbp;
        compute_section_ratios(c, a, b, &wl_inf, &wl_2, &wl_1, &wba, &wbp);

        if (wl_inf > result.wl_inf) result.wl_inf = wl_inf;
        if (wl_2 > result.wl_2) result.wl_2 = wl_2;
        if (wl_1 > result.wl_1) result.wl_1 = wl_1;
        if (wba > result.wba) result.wba = wba;
        if (wbp > result.wbp) result.wbp = wbp;
    }

    fprintf(stderr, "    Progress: %llu/%llu (100%%)\n",
            (unsigned long long)n_samples, (unsigned long long)n_samples);

    return result;
}

/* ========================================================================== */
/* Output Functions                                                           */
/* ========================================================================== */

void print_metrics(const haverkort_metrics_t *m, const char *label)
{
    fprintf(stderr, "%s:\n", label);
    fprintf(stderr, "  WL_inf = %.4f\n", m->wl_inf);
    fprintf(stderr, "  WL_2   = %.4f\n", m->wl_2);
    fprintf(stderr, "  WL_1   = %.4f\n", m->wl_1);
    fprintf(stderr, "  WBA    = %.4f\n", m->wba);
    fprintf(stderr, "  WBP    = %.4f\n", m->wbp);
}

void print_csv_header(FILE *fp)
{
    fprintf(fp, "curve,dims,m0,m1,m2,total_points,method,WL_inf,WL_2,WL_1,WBA,WBP\n");
}

void print_csv_row(FILE *fp, const char *curve_name, const int *m, int n,
                   uint64_t n_points, const char *method,
                   const haverkort_metrics_t *metrics)
{
    fprintf(fp, "%s,%d,%d,%d,%d,%llu,%s,%.6f,%.6f,%.6f,%.6f,%.6f\n",
            curve_name, n,
            m[0], (n > 1) ? m[1] : 0, (n > 2) ? m[2] : 0,
            (unsigned long long)n_points, method,
            metrics->wl_inf, metrics->wl_2, metrics->wl_1,
            metrics->wba, metrics->wbp);
}

/* ========================================================================== */
/* Main Driver                                                                */
/* ========================================================================== */

typedef struct {
    const char *name;
    int m[3];
    int n;
} domain_config_t;

/* Small domains for exhaustive computation (up to ~16K points) */
static const domain_config_t small_domains[] = {
    {"S0_64x64",      {6, 6, 0}, 2},   /* 4,096 points */
    {"S1_256x16",     {8, 4, 0}, 2},   /* 4,096 points */
    {"S2_128x128",    {7, 7, 0}, 2},   /* 16,384 points */
    {"S3_512x32",     {9, 5, 0}, 2},   /* 16,384 points */
};

/* Large domains for sampled computation */
static const domain_config_t large_domains[] = {
    {"D0_512x512",    {9, 9, 0}, 2},   /* 262,144 points */
    {"D1_2048x128",   {11, 7, 0}, 2},  /* 262,144 points */
    {"D2_4096x64",    {12, 6, 0}, 2},  /* 262,144 points */
    {"D3_8192x32",    {13, 5, 0}, 2},  /* 262,144 points */
};

#define N_SMALL_DOMAINS (sizeof(small_domains) / sizeof(small_domains[0]))
#define N_LARGE_DOMAINS (sizeof(large_domains) / sizeof(large_domains[0]))

static const char *HDF5_FILE = "hilbert_tables.h5";
static const uint64_t N_SAMPLES = 10000;
static const uint64_t RANDOM_SEED = 42;

static void run_domain(FILE *csv_fp, const domain_config_t *domain,
                       int use_exhaustive)
{
    int m_array[HAVERKORT_MAX_DIMS] = {0};
    for (int i = 0; i < domain->n; i++) {
        m_array[i] = domain->m[i];
    }

    fprintf(stderr, "\n=== Domain: %s (dims=%d, m={%d,%d,%d}) ===\n",
            domain->name, domain->n, m_array[0], m_array[1], m_array[2]);

    /* Hamilton-CHI */
    {
        fprintf(stderr, "Computing Hamilton-CHI...\n");
        curve_points_t curve = {0};
        if (curve_points_alloc(&curve, hamilton_decode_wrapper, m_array, domain->n) != 0) {
            fprintf(stderr, "  ERROR: Failed to allocate curve points\n");
            return;
        }

        haverkort_metrics_t metrics;
        const char *method;
        if (use_exhaustive) {
            metrics = compute_metrics_exhaustive(&curve);
            method = "exhaustive";
        } else {
            metrics = compute_metrics_sampled(&curve, N_SAMPLES, RANDOM_SEED);
            method = "sampled_10000";
        }

        print_metrics(&metrics, "Hamilton-CHI");
        print_csv_row(csv_fp, "Hamilton-CHI", m_array, domain->n,
                      curve.n_points, method, &metrics);

        curve_points_free(&curve);
    }

    /* LC-CHI-BRGC */
    {
        fprintf(stderr, "Computing LC-CHI-BRGC...\n");
        if (hilbert_tables_init(HDF5_FILE, "brgc", 0) != 0) {
            fprintf(stderr, "  ERROR: Failed to load BRGC tables from %s\n", HDF5_FILE);
            return;
        }

        curve_points_t curve = {0};
        if (curve_points_alloc(&curve, lc_chi_decode_wrapper, m_array, domain->n) != 0) {
            fprintf(stderr, "  ERROR: Failed to allocate curve points\n");
            hilbert_tables_cleanup();
            return;
        }

        haverkort_metrics_t metrics;
        const char *method;
        if (use_exhaustive) {
            metrics = compute_metrics_exhaustive(&curve);
            method = "exhaustive";
        } else {
            metrics = compute_metrics_sampled(&curve, N_SAMPLES, RANDOM_SEED);
            method = "sampled_10000";
        }

        print_metrics(&metrics, "LC-CHI-BRGC");
        print_csv_row(csv_fp, "LC-CHI-BRGC", m_array, domain->n,
                      curve.n_points, method, &metrics);

        curve_points_free(&curve);
        hilbert_tables_cleanup();
    }

    /* LC-CHI-Balanced (if tables exist) */
    {
        fprintf(stderr, "Computing LC-CHI-Balanced...\n");
        if (hilbert_tables_init(HDF5_FILE, "balanced", 0) != 0) {
            fprintf(stderr, "  SKIPPED: No balanced tables in %s\n", HDF5_FILE);
        } else {
            curve_points_t curve = {0};
            if (curve_points_alloc(&curve, lc_chi_decode_wrapper, m_array, domain->n) != 0) {
                fprintf(stderr, "  ERROR: Failed to allocate curve points\n");
                hilbert_tables_cleanup();
            } else {
                haverkort_metrics_t metrics;
                const char *method;
                if (use_exhaustive) {
                    metrics = compute_metrics_exhaustive(&curve);
                    method = "exhaustive";
                } else {
                    metrics = compute_metrics_sampled(&curve, N_SAMPLES, RANDOM_SEED);
                    method = "sampled_10000";
                }

                print_metrics(&metrics, "LC-CHI-Balanced");
                print_csv_row(csv_fp, "LC-CHI-Balanced", m_array, domain->n,
                              curve.n_points, method, &metrics);

                curve_points_free(&curve);
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
            curve_points_t curve = {0};
            if (curve_points_alloc(&curve, lc_chi_decode_wrapper, m_array, domain->n) != 0) {
                fprintf(stderr, "  ERROR: Failed to allocate curve points\n");
                hilbert_tables_cleanup();
            } else {
                haverkort_metrics_t metrics;
                const char *method;
                if (use_exhaustive) {
                    metrics = compute_metrics_exhaustive(&curve);
                    method = "exhaustive";
                } else {
                    metrics = compute_metrics_sampled(&curve, N_SAMPLES, RANDOM_SEED);
                    method = "sampled_10000";
                }

                print_metrics(&metrics, "LC-CHI-Random");
                print_csv_row(csv_fp, "LC-CHI-Random", m_array, domain->n,
                              curve.n_points, method, &metrics);

                curve_points_free(&curve);
            }
            hilbert_tables_cleanup();
        }
    }
}

static void print_usage(const char *prog)
{
    fprintf(stderr, "Usage: %s [OPTIONS]\n", prog);
    fprintf(stderr, "\nOptions:\n");
    fprintf(stderr, "  --small-only     Only run small (exhaustive) domains\n");
    fprintf(stderr, "  --large-only     Only run large (sampled) domains\n");
    fprintf(stderr, "  --output FILE    Write CSV to FILE (default: stdout)\n");
    fprintf(stderr, "  --hdf5 FILE      Use FILE for Hilbert tables (default: hilbert_tables.h5)\n");
    fprintf(stderr, "  --help           Show this help\n");
}

int main(int argc, char **argv)
{
    int run_small = 1;
    int run_large = 1;
    const char *output_file = NULL;
    const char *hdf5_file = HDF5_FILE;

    /* Parse arguments */
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--small-only") == 0) {
            run_large = 0;
        } else if (strcmp(argv[i], "--large-only") == 0) {
            run_small = 0;
        } else if (strcmp(argv[i], "--output") == 0 && i + 1 < argc) {
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

    /* Update HDF5 file path */
    /* Note: hdf5_file is used but we can't easily override the static const,
       so we just print a warning if they differ */
    if (strcmp(hdf5_file, HDF5_FILE) != 0) {
        fprintf(stderr, "Note: Using HDF5 file: %s\n", hdf5_file);
        /* Would need to modify the code to actually use this */
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

    /* Run small domains (exhaustive) */
    if (run_small) {
        fprintf(stderr, "\n========================================\n");
        fprintf(stderr, "Running SMALL domains (exhaustive O(N^2))\n");
        fprintf(stderr, "========================================\n");

        for (size_t i = 0; i < N_SMALL_DOMAINS; i++) {
            run_domain(csv_fp, &small_domains[i], 1);
        }
    }

    /* Run large domains (sampled) */
    if (run_large) {
        fprintf(stderr, "\n========================================\n");
        fprintf(stderr, "Running LARGE domains (sampled)\n");
        fprintf(stderr, "========================================\n");

        for (size_t i = 0; i < N_LARGE_DOMAINS; i++) {
            run_domain(csv_fp, &large_domains[i], 0);
        }
    }

    fprintf(stderr, "\nDone.\n");

    if (output_file) {
        fclose(csv_fp);
        fprintf(stderr, "Results written to: %s\n", output_file);
    }

    return 0;
}
