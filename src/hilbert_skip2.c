/*
 * hilbert_skip2.c
 *
 * Skip-2 Hilbert iteration: compute p₂ = H(h+2) from p₀ = H(h)
 * without explicitly computing the intermediate point p₁.
 *
 * Key insight: we need the intermediate STATE but not the intermediate POINT.
 * State updates are cheap; point reconstruction is expensive.
 */

#include <stdint.h>
#include <string.h>
#include <stdbool.h>

#define MAX_DIMS 32
#define MAX_LEVELS 64

typedef __uint128_t hindex_t;
typedef uint32_t coord_t;

/* --------------------------------------------------------------------------
 * Bit manipulation (same as before)
 * -------------------------------------------------------------------------- */

static inline uint32_t gray_code(uint32_t i) { return i ^ (i >> 1); }
static inline uint32_t mask_bits(int bits) { return bits > 0 ? ((1U << bits) - 1) : 0; }

static inline uint32_t lrotate(uint32_t x, int r, int bits) {
    if (bits <= 0) return x;
    r = r % bits;
    x &= mask_bits(bits);
    if (r == 0) return x;
    return ((x << r) | (x >> (bits - r))) & mask_bits(bits);
}

static inline uint32_t T_inv(uint32_t e, int d, int bits, uint32_t b) {
    return (lrotate(b & mask_bits(bits), (d + 1) % bits, bits) ^ e) & mask_bits(bits);
}

static inline int trailing_zeros(uint32_t x) {
    if (x == 0) return 32;
    int c = 0;
    while ((x & 1) == 0) { c++; x >>= 1; }
    return c;
}

static inline int trailing_ones(uint32_t i) {
    int c = 0;
    while (i & 1) { c++; i >>= 1; }
    return c;
}

static inline uint32_t e_seq(int i) {
    if (i == 0) return 0;
    return gray_code(2 * ((i - 1) / 2));
}

static inline int d_seq(int bits, int i) {
    if (i == 0) return 0;
    if (i & 1) return trailing_ones(i) % bits;
    return trailing_ones(i - 1) % bits;
}

/* --------------------------------------------------------------------------
 * Minimal state for skip-2 computation
 *
 * For skip-2, we track state at each level but DON'T store the point.
 * -------------------------------------------------------------------------- */

typedef struct {
    int n;
    int mmax;
    int m[MAX_DIMS];
    int k[MAX_LEVELS + 1];
    int A[MAX_LEVELS + 1][MAX_DIMS];
    uint32_t w[MAX_LEVELS + 1];
    uint32_t e[MAX_LEVELS + 1];
    int d[MAX_LEVELS + 1];
    hindex_t h;
} hilbert_state_t;

/* Axis ordering */
typedef struct { int axis; int exp; } axis_exp_t;

static void sort_axes_by_exp(const int *m, int n, int *order) {
    axis_exp_t items[MAX_DIMS];
    for (int i = 0; i < n; i++) { items[i].axis = i; items[i].exp = m[i]; }
    for (int i = 1; i < n; i++) {
        axis_exp_t key = items[i];
        int j = i - 1;
        while (j >= 0 && (items[j].exp > key.exp ||
               (items[j].exp == key.exp && items[j].axis > key.axis))) {
            items[j + 1] = items[j]; j--;
        }
        items[j + 1] = key;
    }
    for (int i = 0; i < n; i++) order[i] = items[i].axis;
}

static int get_active_axes(const int *m, int n, int s, const int *order, int *active) {
    int k = 0;
    for (int i = 0; i < n; i++) {
        int ax = order[i];
        if (m[ax] >= s) active[k++] = ax;
    }
    return k;
}

static void embed_state(const int *A_old, int k_old, const int *A_new, int k_new,
                        uint32_t e_old, int d_old, uint32_t *e_new, int *d_new) {
    int pos_new[MAX_DIMS];
    for (int j = 0; j < k_new; j++) pos_new[A_new[j]] = j;
    *e_new = 0;
    for (int j = 0; j < k_old; j++) {
        if ((e_old >> j) & 1) *e_new |= 1U << pos_new[A_old[j]];
    }
    *d_new = pos_new[A_old[d_old]];
}

/* --------------------------------------------------------------------------
 * Core: compute single-step delta without updating point
 *
 * Returns the axis and direction for h → h+1, and updates the state.
 * -------------------------------------------------------------------------- */

typedef struct {
    int axis;       /* physical axis that changes (-1 if overflow) */
    int direction;  /* +1 or -1 */
} step_delta_t;

/*
 * Compute the coordinate delta for incrementing h by 1.
 * Updates state in place. Does NOT touch any point array.
 */
static step_delta_t compute_step_delta(hilbert_state_t *state) {
    step_delta_t result = {-1, 0};
    int mmax = state->mmax;
    if (mmax == 0) return result;

    /* Find carry level */
    int s_star = 1;
    while (s_star <= mmax) {
        if (state->w[s_star] < (uint32_t)((1 << state->k[s_star]) - 1)) break;
        s_star++;
    }
    if (s_star > mmax) return result;  /* overflow */

    /* Get state at carry level */
    uint32_t w = state->w[s_star];
    uint32_t e = state->e[s_star];
    int d = state->d[s_star];
    int k = state->k[s_star];
    int *A = state->A[s_star];

    /* Which Gray code bit flips? */
    uint32_t gc_old = gray_code(w);
    uint32_t gc_new = gray_code(w + 1);
    int g = trailing_zeros(gc_old ^ gc_new);

    /* After T⁻¹, the changed local axis is (g + d + 1) mod k */
    int g_local = (g + d + 1) % k;
    result.axis = A[g_local];

    /* Direction from bit value in l_new */
    uint32_t l_new = T_inv(e, d, k, gc_new);
    result.direction = ((l_new >> g_local) & 1) ? +1 : -1;

    /* Update digits */
    for (int s = 1; s < s_star; s++) state->w[s] = 0;
    state->w[s_star] = w + 1;
    state->h += 1;

    /* Recompute state from s_star downward */
    uint32_t e_curr = state->e[s_star];
    int d_curr = state->d[s_star];

    for (int s = s_star; s >= 1; s--) {
        int k_s = state->k[s];
        uint32_t w_s = state->w[s];

        state->e[s] = e_curr;
        state->d[s] = d_curr;

        e_curr = e_curr ^ lrotate(e_seq(w_s), (d_curr + 1) % k_s, k_s);
        d_curr = (d_curr + d_seq(k_s, w_s) + 1) % k_s;

        if (s > 1 && state->k[s - 1] > k_s) {
            uint32_t e_new; int d_new;
            embed_state(state->A[s], k_s, state->A[s - 1], state->k[s - 1],
                        e_curr, d_curr, &e_new, &d_new);
            e_curr = e_new; d_curr = d_new;
        }
    }

    return result;
}

/* --------------------------------------------------------------------------
 * Skip-2: compute p₂ from p₀ without computing p₁
 * -------------------------------------------------------------------------- */

/*
 * Compute coordinate deltas for h → h+2 in one call.
 * Returns two step_delta_t values.
 *
 * The key insight: we update the STATE twice, but never compute
 * the intermediate POINT. State updates are O(mmax), point
 * reconstruction would be O(mmax × n).
 */
typedef struct {
    step_delta_t step1;
    step_delta_t step2;
    /* Derived: net change */
    int net_axes[2];     /* axes that change (up to 2), -1 if unused */
    int net_deltas[2];   /* corresponding deltas */
    int n_changes;       /* 0, 1, or 2 */
} skip2_result_t;

skip2_result_t hilbert_skip2_delta(hilbert_state_t *state) {
    skip2_result_t result;

    /* Step 1: h → h+1 (updates state, no point) */
    result.step1 = compute_step_delta(state);

    /* Step 2: h+1 → h+2 (updates state again, no point) */
    result.step2 = compute_step_delta(state);

    /* Compute net change */
    if (result.step1.axis < 0 || result.step2.axis < 0) {
        /* Overflow in one or both steps */
        result.n_changes = 0;
        result.net_axes[0] = result.net_axes[1] = -1;
        result.net_deltas[0] = result.net_deltas[1] = 0;
    } else if (result.step1.axis == result.step2.axis) {
        /* Same axis: deltas combine */
        int net = result.step1.direction + result.step2.direction;
        if (net == 0) {
            /* Canceled out! p₂ = p₀ */
            result.n_changes = 0;
            result.net_axes[0] = result.net_axes[1] = -1;
            result.net_deltas[0] = result.net_deltas[1] = 0;
        } else {
            /* Net ±2 in one axis */
            result.n_changes = 1;
            result.net_axes[0] = result.step1.axis;
            result.net_deltas[0] = net;  /* +2 or -2 */
            result.net_axes[1] = -1;
            result.net_deltas[1] = 0;
        }
    } else {
        /* Different axes: two independent changes */
        result.n_changes = 2;
        result.net_axes[0] = result.step1.axis;
        result.net_deltas[0] = result.step1.direction;
        result.net_axes[1] = result.step2.axis;
        result.net_deltas[1] = result.step2.direction;
    }

    return result;
}

/*
 * Apply skip-2 to a point array.
 * state should be initialized at h, point should be p = H(h).
 * After this call, state is at h+2 and point is updated to H(h+2).
 */
void hilbert_apply_skip2(hilbert_state_t *state, coord_t *point) {
    skip2_result_t r = hilbert_skip2_delta(state);

    for (int i = 0; i < r.n_changes; i++) {
        if (r.net_axes[i] >= 0) {
            point[r.net_axes[i]] += r.net_deltas[i];
        }
    }
}

/* --------------------------------------------------------------------------
 * For parallelization: initialize state at arbitrary h
 *
 * This is the key for breaking loop dependencies across chunks.
 * Each parallel worker can initialize at chunk_start and iterate from there.
 * -------------------------------------------------------------------------- */

void hilbert_state_init(hilbert_state_t *state, hindex_t h,
                        const int *m, int n) {
    memset(state, 0, sizeof(*state));
    if (n <= 0 || n > MAX_DIMS) return;

    state->n = n;
    state->h = h;
    memcpy(state->m, m, n * sizeof(int));

    int mmax = 0, total_bits = 0;
    for (int i = 0; i < n; i++) {
        if (m[i] > mmax) mmax = m[i];
        total_bits += m[i];
    }
    state->mmax = mmax;
    if (mmax == 0) return;

    int order[MAX_DIMS];
    sort_axes_by_exp(m, n, order);

    for (int s = 1; s <= mmax; s++) {
        state->k[s] = get_active_axes(m, n, s, order, state->A[s]);
    }

    /* Extract digits and compute state at each level */
    int bit_pos = total_bits;
    uint32_t e = 0;
    int d = 0;

    for (int s = mmax; s >= 1; s--) {
        int k = state->k[s];
        bit_pos -= k;
        uint32_t w = (uint32_t)((h >> bit_pos) & mask_bits(k));

        state->w[s] = w;
        state->e[s] = e;
        state->d[s] = d;

        /* State update (without point reconstruction) */
        e = e ^ lrotate(e_seq(w), (d + 1) % k, k);
        d = (d + d_seq(k, w) + 1) % k;

        if (s > 1 && state->k[s - 1] > k) {
            uint32_t e_new; int d_new;
            embed_state(state->A[s], k, state->A[s - 1], state->k[s - 1],
                        e, d, &e_new, &d_new);
            e = e_new; d = d_new;
        }
    }
}

/* --------------------------------------------------------------------------
 * Generalized skip-N (preview of the approach)
 * -------------------------------------------------------------------------- */

/*
 * For skip-N where N > 2, the same principle applies:
 * 1. Simulate N state transitions (cheap)
 * 2. Track which axes change and by how much
 * 3. Apply net changes to point
 *
 * The state simulation is O(N × mmax) worst case, but often much better
 * because most steps only affect level 1.
 *
 * For arbitrary jumps (h → h + k for large k), it's better to do a
 * fresh decode at h + k. The crossover point depends on k vs mmax × n.
 */

/* --------------------------------------------------------------------------
 * Test
 * -------------------------------------------------------------------------- */

#ifdef TEST_SKIP2

#include <stdio.h>

/* Reference from anisotropic_hilbert.c */
extern void hilbert_decode(hindex_t h, const int *m, int n, coord_t *point);

int main() {
    int m[] = {3, 3, 2};  /* 8 × 8 × 4 box */
    int n = 3;
    int total_bits = m[0] + m[1] + m[2];
    uint64_t max_h = (1ULL << total_bits) - 1;

    printf("Testing skip-2 on 8×8×4 box (h_max = %llu)\n",
           (unsigned long long)max_h);
    printf("================================================\n\n");

    /* Initialize state and get p0 via full decode */
    hilbert_state_t state;
    hilbert_state_init(&state, 0, m, n);

    coord_t point[3];
    hilbert_decode(0, m, n, point);

    int errors = 0;
    int cancellations = 0;  /* cases where p₂ = p₀ */

    printf("Checking all skip-2 transitions...\n");

    for (uint64_t h = 0; h + 2 <= max_h; h += 2) {
        /* Reset state and point to h */
        hilbert_state_init(&state, h, m, n);
        hilbert_decode(h, m, n, point);

        /* Apply skip-2 */
        skip2_result_t r = hilbert_skip2_delta(&state);

        coord_t p2_skip[3];
        memcpy(p2_skip, point, sizeof(p2_skip));
        for (int i = 0; i < r.n_changes; i++) {
            if (r.net_axes[i] >= 0) {
                p2_skip[r.net_axes[i]] += r.net_deltas[i];
            }
        }

        /* Get reference p₂ */
        coord_t p2_ref[3];
        hilbert_decode(h + 2, m, n, p2_ref);

        /* Compare */
        bool match = (p2_skip[0] == p2_ref[0] &&
                      p2_skip[1] == p2_ref[1] &&
                      p2_skip[2] == p2_ref[2]);

        if (!match) {
            printf("  ERROR at h=%llu: skip=(%u,%u,%u) ref=(%u,%u,%u)\n",
                   (unsigned long long)h,
                   p2_skip[0], p2_skip[1], p2_skip[2],
                   p2_ref[0], p2_ref[1], p2_ref[2]);
            errors++;
        }

        if (r.n_changes == 0) {
            cancellations++;
        }
    }

    printf("\nResults:\n");
    printf("  Errors: %d\n", errors);
    printf("  Cancellations (p₂ = p₀): %d\n", cancellations);

    /* Show some examples of each case */
    printf("\nExamples of different cases:\n");

    int shown[3] = {0, 0, 0};  /* shown count for 0, 1, 2 changes */

    for (uint64_t h = 0; h + 2 <= max_h && (shown[0] < 2 || shown[1] < 2 || shown[2] < 2); h++) {
        hilbert_state_init(&state, h, m, n);

        coord_t p0[3], p1[3], p2[3];
        hilbert_decode(h, m, n, p0);
        hilbert_decode(h + 1, m, n, p1);
        hilbert_decode(h + 2, m, n, p2);

        skip2_result_t r;
        hilbert_state_init(&state, h, m, n);
        r = hilbert_skip2_delta(&state);

        if (shown[r.n_changes] < 2) {
            printf("\n  h=%llu: n_changes=%d\n", (unsigned long long)h, r.n_changes);
            printf("    p₀=(%u,%u,%u) → p₁=(%u,%u,%u) → p₂=(%u,%u,%u)\n",
                   p0[0], p0[1], p0[2], p1[0], p1[1], p1[2], p2[0], p2[1], p2[2]);
            printf("    step1: axis=%d, dir=%+d\n", r.step1.axis, r.step1.direction);
            printf("    step2: axis=%d, dir=%+d\n", r.step2.axis, r.step2.direction);
            if (r.n_changes > 0) {
                printf("    net: ");
                for (int i = 0; i < r.n_changes; i++) {
                    printf("axis[%d] %+d  ", r.net_axes[i], r.net_deltas[i]);
                }
                printf("\n");
            }
            shown[r.n_changes]++;
        }
    }

    return errors;
}

#endif /* TEST_SKIP2 */
