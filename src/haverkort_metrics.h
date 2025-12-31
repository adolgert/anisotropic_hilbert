/*
 * haverkort_metrics.h
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

#ifndef HAVERKORT_METRICS_H
#define HAVERKORT_METRICS_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define HAVERKORT_MAX_DIMS 8

/*
 * Structure to hold all Haverkort metrics for a curve.
 */
typedef struct {
    double wl_inf;   /* WL_infinity - worst-case Chebyshev locality */
    double wl_2;     /* WL_2 - worst-case Euclidean locality */
    double wl_1;     /* WL_1 - worst-case Manhattan locality */
    double wba;      /* WBA - worst-case bounding box area ratio */
    double wbp;      /* WBP - worst-case bounding box squared perimeter ratio */
} haverkort_metrics_t;

/*
 * Precomputed curve representation: all points decoded and stored.
 */
typedef struct {
    uint32_t *points;       /* Array of N * n_dims coordinates */
    uint64_t n_points;      /* Total number of points */
    int n_dims;             /* Number of dimensions */
    int m[HAVERKORT_MAX_DIMS]; /* Bits per axis */
} curve_points_t;

/*
 * Callback type for decoding a Hilbert index to a point.
 *
 * Parameters:
 *   h     - Hilbert index
 *   m     - array of n exponents (bits per axis)
 *   n     - number of dimensions
 *   point - output array of n coordinates
 */
typedef void (*decode_fn_t)(uint64_t h, const int *m, int n, uint32_t *point);

/*
 * Precompute all points along the curve.
 * Caller must free points->points when done.
 *
 * Returns 0 on success, -1 on error.
 */
int curve_points_alloc(curve_points_t *points, decode_fn_t decode,
                       const int *m, int n);

/*
 * Free memory allocated by curve_points_alloc.
 */
void curve_points_free(curve_points_t *points);

/*
 * Get pointer to coordinates of point at index h.
 */
static inline const uint32_t *curve_point_at(const curve_points_t *c, uint64_t h)
{
    return c->points + h * (uint64_t)c->n_dims;
}

/*
 * Compute Haverkort metrics using exhaustive O(N^2) enumeration.
 * Suitable for small domains (N <= ~16K points).
 *
 * This examines every pair (a, b) with a <= b and computes all metric ratios.
 */
haverkort_metrics_t compute_metrics_exhaustive(const curve_points_t *curve);

/*
 * Compute Haverkort metrics using random sampling.
 * Suitable for large domains.
 *
 * Samples n_samples random curve sections with log-uniform length distribution.
 *
 * seed: random seed for reproducibility (0 = use time)
 */
haverkort_metrics_t compute_metrics_sampled(const curve_points_t *curve,
                                            uint64_t n_samples, uint64_t seed);

/*
 * Print metrics to stdout in human-readable format.
 */
void print_metrics(const haverkort_metrics_t *m, const char *label);

/*
 * Print CSV header line to file.
 */
void print_csv_header(FILE *fp);

/*
 * Print a single row of CSV data for one curve/domain configuration.
 *
 * curve_name: e.g., "Hamilton-CHI", "LC-CHI-BRGC"
 * method: e.g., "exhaustive", "sampled_10000"
 */
void print_csv_row(FILE *fp, const char *curve_name, const int *m, int n,
                   uint64_t n_points, const char *method,
                   const haverkort_metrics_t *metrics);

#ifdef __cplusplus
}
#endif

#endif /* HAVERKORT_METRICS_H */
