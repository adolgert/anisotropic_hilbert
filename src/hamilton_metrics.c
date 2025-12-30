/*
 * hamilton_metrics.c
 *
 * Measures discontinuities in Hamilton's Compact Hilbert Index implementation
 * and outputs results to CSV for paper tables.
 *
 * Output CSV columns:
 *   dims, m0, m1, m2, total_points, discontinuity_count, max_distance, geom_mean_distance
 *
 * For 2D runs, m2 = 0
 * geom_mean_distance = geometric mean of all jump distances (exp(mean(log(distances))))
 * If no discontinuities, max_distance = 0 and geom_mean_distance = 0
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>

/* Include the Hamilton implementation directly */
#include "hamilton.c"

/*
 * Compute discontinuity metrics for a given configuration.
 *
 * Parameters:
 *   n            - number of dimensions
 *   m            - array of n exponents (bits per axis)
 *   count        - output: number of discontinuities (steps with distance != 1)
 *   max_dist     - output: maximum Manhattan distance among all steps
 *   geom_mean    - output: geometric mean of distances for discontinuities
 */
static void compute_discontinuities(int n, const int *m,
                                    uint64_t *count, int *max_dist, double *geom_mean)
{
    int total_bits = 0;
    for (int i = 0; i < n; i++)
        total_bits += m[i];

    hamilton_index_t max_h = ((hamilton_index_t)1 << total_bits);

    *count = 0;
    *max_dist = 0;
    double log_sum = 0.0;

    hamilton_coord_t p1[HAMILTON_MAX_DIMS], p2[HAMILTON_MAX_DIMS];

    /* Decode the first point */
    hamilton_decode(0, m, n, p1);

    for (hamilton_index_t h = 0; h + 1 < max_h; h++)
    {
        hamilton_decode(h + 1, m, n, p2);

        /* Compute Manhattan distance */
        int dist = 0;
        for (int i = 0; i < n; i++)
        {
            int d = (int)p2[i] - (int)p1[i];
            dist += (d < 0) ? -d : d;
        }

        if (dist != 1)
        {
            (*count)++;
            if (dist > *max_dist)
                *max_dist = dist;
            log_sum += log((double)dist);
        }

        /* Move p2 -> p1 for next iteration */
        for (int i = 0; i < n; i++)
            p1[i] = p2[i];
    }

    /* Compute geometric mean */
    if (*count > 0)
        *geom_mean = exp(log_sum / (double)(*count));
    else
        *geom_mean = 0.0;
}

int main(int argc, char **argv)
{
    (void)argc;
    (void)argv;

    /* Print CSV header */
    printf("dims,m0,m1,m2,total_points,discontinuity_count,max_distance,geom_mean_distance\n");

    int config_count = 0;

    /* 2D configurations: m0, m1 in [1, 12] */
    fprintf(stderr, "Running 2D configurations (144 total)...\n");
    for (int m0 = 1; m0 <= 12; m0++)
    {
        for (int m1 = 1; m1 <= 12; m1++)
        {
            int m[] = {m0, m1};
            int n = 2;
            int total_bits = m0 + m1;
            uint64_t total_points = (uint64_t)1 << total_bits;

            uint64_t count;
            int max_dist;
            double geom_mean;

            compute_discontinuities(n, m, &count, &max_dist, &geom_mean);

            printf("%d,%d,%d,%d,%llu,%llu,%d,%.6f\n",
                   n, m0, m1, 0,
                   (unsigned long long)total_points,
                   (unsigned long long)count,
                   max_dist,
                   geom_mean);

            config_count++;
            if (config_count % 10 == 0)
                fprintf(stderr, "  Progress: %d configurations done\n", config_count);
        }
    }

    /* 3D configurations: m0, m1, m2 in [1, 7] */
    fprintf(stderr, "Running 3D configurations (343 total)...\n");
    for (int m0 = 1; m0 <= 7; m0++)
    {
        for (int m1 = 1; m1 <= 7; m1++)
        {
            for (int m2 = 1; m2 <= 7; m2++)
            {
                int m[] = {m0, m1, m2};
                int n = 3;
                int total_bits = m0 + m1 + m2;
                uint64_t total_points = (uint64_t)1 << total_bits;

                uint64_t count;
                int max_dist;
                double geom_mean;

                compute_discontinuities(n, m, &count, &max_dist, &geom_mean);

                printf("%d,%d,%d,%d,%llu,%llu,%d,%.6f\n",
                       n, m0, m1, m2,
                       (unsigned long long)total_points,
                       (unsigned long long)count,
                       max_dist,
                       geom_mean);

                config_count++;
                if (config_count % 10 == 0)
                    fprintf(stderr, "  Progress: %d configurations done\n", config_count);
            }
        }
    }

    fprintf(stderr, "Done. Total configurations: %d\n", config_count);

    return 0;
}
