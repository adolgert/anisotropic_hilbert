/*
 * hilbert_affine.c
 *
 * Anisotropic (activation) Hilbert encode/decode using the affine-map
 * formulation from lean/refine_affine_aniso.md.
 *
 * - Axes are labeled 0..n-1.
 * - At level s (MSB-first), active axes are those with m_j >= s, ordered by
 *   priority (m_j, j).
 * - The per-level state is the affine map S_{e,delta}(x) = rotL(delta) x XOR e
 *   on the active list (delta = d+1).
 * - Digits are variable-width (k_s bits) and are packed MSB-first into the
 *   Hilbert index.
 *
 * Coordinate type is uint32_t, so each m_j must be in [0, 32].
 * Hilbert indices use __uint128_t; sum(m_j) must be <= 128.
 */

#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>

#define MAX_DIMS 32
#define MAX_LEVELS 32
#define MAX_INDEX_BITS 128

typedef __uint128_t hindex_t;
typedef uint32_t coord_t;

typedef struct
{
  uint32_t e; /* entry mask in the current active list */
  uint32_t d; /* direction index in the current active list */
} hilbert_state_t;

typedef struct
{
  int mmax;                    /* max(extents bits) */
  int total_bits;              /* sum(extents bits)*/
  int k_level[MAX_LEVELS + 1]; /* Number of active axes at level */
  int axes_ordered[MAX_DIMS];
} hilbert_curve_t;

static inline uint32_t mask_bits(uint32_t bits)
{
  return (bits >= 32u) ? 0xFFFFFFFFu : ((1u << bits) - 1u);
}

static inline uint32_t rotl_bits(uint32_t x, uint32_t r, uint32_t bits)
{
  if (bits == 0u)
    return x;
  if (bits == 32u)
  {
    r &= 31u;
    return (r == 0u) ? x : (uint32_t)((x << r) | (x >> (32u - r)));
  }
  const uint32_t mask = mask_bits(bits);
  x &= mask;
  r %= bits;
  if (r == 0u)
    return x;
  return (uint32_t)(((x << r) | (x >> (bits - r))) & mask);
}

static inline uint32_t rotr_bits(uint32_t x, uint32_t r, uint32_t bits)
{
  if (bits == 0u)
    return x;
  if (bits == 32u)
  {
    r &= 31u;
    return (r == 0u) ? x : (uint32_t)((x >> r) | (x << (32u - r)));
  }
  const uint32_t mask = mask_bits(bits);
  x &= mask;
  r %= bits;
  if (r == 0u)
    return x;
  return (uint32_t)(((x >> r) | (x << (bits - r))) & mask);
}

static inline uint32_t gray_code(uint32_t x)
{
  return x ^ (x >> 1);
}

static inline uint32_t gray_decode(uint32_t g)
{
  uint32_t x = g;
  x ^= x >> 1;
  x ^= x >> 2;
  x ^= x >> 4;
  x ^= x >> 8;
  x ^= x >> 16;
  return x;
}

/*
 * Gray code with exit at axis 0 (fixed orientation).
 * Standard BRGC exits at axis k-1; rotating by 1 moves exit to axis 0.
 * Hamilton's paper had a conceptual difficulty where it conflated the
 * direction of the child hypercube orientation with the rotation, but
 * the BRGC orientation was in the last axis. This brings the two into
 * agreement.
 */
static inline uint32_t gray_code_axis0(uint32_t w, uint32_t k)
{
  return rotl_bits(gray_code(w), 1u, k);
}

static inline uint32_t gray_decode_axis0(uint32_t g, uint32_t k)
{
  return gray_decode(rotr_bits(g, 1u, k));
}

static inline uint32_t trailing_ones(uint32_t x)
{
  uint32_t c = 0;
  while ((x & 1u) != 0u)
  {
    c++;
    x >>= 1;
  }
  return c;
}

/* Hamilton entry sequence e(w) for a k-dimensional cube. */
static inline uint32_t child_entry(uint32_t w, uint32_t k)
{
  if (w == 0u)
    return 0u;
  return rotl_bits(gray_code((w - 1u) & ~1u), 1, k);
}

/* Hamilton direction sequence d(w) for a k-dimensional cube. */
static inline uint32_t child_dir(uint32_t w, uint32_t k)
{
  if (w == 0u)
    return 1u;
  if ((w & 1u) != 0u)
    return (trailing_ones(w) + 1) % k;
  return (trailing_ones(w - 1u) + 1) % k;
}

/* S_{e,d}(x) = rotL(d) x XOR e. */
static inline uint32_t affine_apply(uint32_t x, uint32_t e, uint32_t d, uint32_t k)
{
  return (rotl_bits(x, d, k) ^ e) & mask_bits(k);
}

/* S^{-1}(y) = rotR(d) (y XOR e). */
static inline uint32_t affine_apply_inv(uint32_t y, uint32_t e, uint32_t d, uint32_t k)
{
  return rotr_bits((y ^ e), d, k) & mask_bits(k);
}

typedef struct
{
  int axis;
  int exp;
} axis_exp_t;

/* Sort axes by priority (m_j, j). */
static void sort_axes_by_priority(const int *m, int n, int *order)
{
  axis_exp_t items[MAX_DIMS];
  for (int i = 0; i < n; i++)
  {
    items[i].axis = i;
    items[i].exp = m[i];
  }
  for (int i = 1; i < n; i++)
  {
    axis_exp_t key = items[i];
    int j = i - 1;
    while (j >= 0 && (items[j].exp < key.exp ||
                      (items[j].exp == key.exp && items[j].axis < key.axis)))
    {
      items[j + 1] = items[j];
      j--;
    }
    items[j + 1] = key;
  }
  for (int i = 0; i < n; i++)
  {
    order[i] = items[i].axis;
  }
}

static bool build_active_axes(const int *m, int n, hilbert_curve_t *curve)
{
  if (!m || n <= 0 || n > MAX_DIMS || !curve)
    return false;

  int mmax = 0;
  int total_bits = 0;
  for (int i = 0; i < n; i++)
  {
    if (m[i] < 0 || m[i] > MAX_LEVELS)
      return false;
    if (m[i] > mmax)
      mmax = m[i];
    total_bits += m[i];
  }
  if (total_bits > MAX_INDEX_BITS)
    return false;

  curve->mmax = mmax;
  curve->total_bits = total_bits;

  sort_axes_by_priority(m, n, curve->axes_ordered);
  curve->k_level[0] = 0;

  int axis_idx = n;
  for (int s = 1; s <= mmax; s++)
  {
    while (axis_idx > 0 && m[curve->axes_ordered[axis_idx - 1]] < s)
    {
      axis_idx--;
    }
    curve->k_level[s] = axis_idx;
  }

  return true;
}

/*
 * Gather bits from coordinates into a plane value.
 * Collects bit (s-1) from each active axis into a k-bit plane.
 */
static inline uint32_t gather_plane(const coord_t *point, const int *A, int k, int s)
{
  uint32_t plane = 0u;
  for (int j = 0; j < k; j++)
  {
    int ax = A[j];
    plane |= ((point[ax] >> (s - 1)) & 1u) << j;
  }
  return plane;
}

/*
 * Scatter bits from a plane value to coordinates.
 * Distributes each bit of the k-bit plane to bit (s-1) of the corresponding axis.
 */
static inline void scatter_plane(coord_t *point, const int *A, int k, int s, uint32_t plane)
{
  for (int j = 0; j < k; j++)
  {
    int ax = A[j];
    point[ax] |= ((plane >> j) & 1u) << (s - 1);
  }
}

hindex_t hilbert_affine_encode(const coord_t *point, const int *m, int n)
{
  hilbert_curve_t curve = {0};

  if (!point || !m)
    return (hindex_t)0;
  if (!build_active_axes(m, n, &curve))
  {
    return (hindex_t)0;
  }
  if (curve.mmax == 0)
    return (hindex_t)0;

  hilbert_state_t st = {0u, 0u};
  hindex_t h = 0;
  uint32_t plane, pre, w = 0;

  for (int s = curve.mmax; s >= 2; s--)
  {
    int k = curve.k_level[s];
    assert(k != 0);

    uint32_t mask = mask_bits((uint32_t)k);
    plane = gather_plane(point, curve.axes_ordered, k, s);
    pre = affine_apply_inv(plane, st.e, st.d, (uint32_t)k);
    w = gray_decode_axis0(pre, (uint32_t)k) & mask;

    h = (h << k) | (hindex_t)w;

    /* State update for next level */
    uint32_t entry = child_entry(w, k) & mask;
    st.e = affine_apply(entry, st.e, st.d, (uint32_t)k);
    st.d = (st.d + child_dir(w, (uint32_t)k)) % (uint32_t)k;
  }

  int k = curve.k_level[1];
  assert(k != 0);

  uint32_t mask = mask_bits((uint32_t)k);
  plane = gather_plane(point, curve.axes_ordered, k, 1);
  pre = affine_apply_inv(plane, st.e, st.d, (uint32_t)k);
  w = gray_decode_axis0(pre, (uint32_t)k) & mask;

  h = (h << k) | (hindex_t)w;

  return h;
}

void hilbert_affine_decode(hindex_t h, const int *m, int n, coord_t *point)
{
  if (!point || !m || n <= 0 || n > MAX_DIMS)
    return;
  memset(point, 0, (size_t)n * sizeof(coord_t));

  hilbert_curve_t curve = {0};

  if (!build_active_axes(m, n, &curve))
  {
    return;
  }
  if (curve.mmax == 0)
    return;

  int bit_pos = curve.total_bits;
  hilbert_state_t st = {0u, 0u};
  uint32_t g, plane, w = 0;

  for (int s = curve.mmax; s >= 2; s--)
  {
    int k = curve.k_level[s];
    assert(k != 0);

    uint32_t mask = mask_bits((uint32_t)k);

    bit_pos -= k;
    w = (uint32_t)((h >> bit_pos) & (hindex_t)mask);

    g = gray_code_axis0(w, (uint32_t)k);
    plane = affine_apply(g, st.e, st.d, (uint32_t)k);
    scatter_plane(point, curve.axes_ordered, k, s, plane);

    /* State update for next level */
    uint32_t entry = child_entry(w, k) & mask;
    st.e = affine_apply(entry, st.e, st.d, (uint32_t)k);
    st.d = (st.d + child_dir(w, (uint32_t)k)) % (uint32_t)k;
  }

  /* Last level (s = 1): no state update needed afterward */
  int k = curve.k_level[1];
  assert(k != 0);

  uint32_t mask = mask_bits((uint32_t)k);

  bit_pos -= k;
  w = (uint32_t)((h >> bit_pos) & (hindex_t)mask);

  g = gray_code_axis0(w, (uint32_t)k);
  plane = affine_apply(g, st.e, st.d, (uint32_t)k);
  scatter_plane(point, curve.axes_ordered, k, 1, plane);
}

uint64_t hilbert_affine_encode_64(const coord_t *point, const int *m, int n)
{
  return (uint64_t)hilbert_affine_encode(point, m, n);
}

void hilbert_affine_decode_64(uint64_t h, const int *m, int n, coord_t *point)
{
  hilbert_affine_decode((hindex_t)h, m, n, point);
}

void hilbert_affine_encode_128(const coord_t *point, const int *m, int n,
                               uint64_t *h_lo, uint64_t *h_hi)
{
  hindex_t h = hilbert_affine_encode(point, m, n);
  *h_lo = (uint64_t)h;
  *h_hi = (uint64_t)(h >> 64);
}

void hilbert_affine_decode_128(uint64_t h_lo, uint64_t h_hi, const int *m, int n,
                               coord_t *point)
{
  hindex_t h = ((hindex_t)h_hi << 64) | h_lo;
  hilbert_affine_decode(h, m, n, point);
}

/*
 * Enumerate all points in increasing Hilbert index using a stack of affine
 * states per level. This matches the conventions in hilbert_affine.c:
 *  - digits are variable-width (k_level[s] bits) in mixed radix
 *  - affine state is (e,d) with S_{e,d}(x)=rotL(d)x XOR e on k active axes
 *  - axis activation handled by the same (e<<=shift; d+=shift) embedding
 */

typedef void (*hilbert_emit_fn)(hindex_t h, const coord_t *p, int n, void *ctx);

static inline void toggle_scatter_delta(coord_t *point,
                                        const int *A, int k, int s,
                                        uint32_t delta_plane)
{
  for (int j = 0; j < k; j++)
  {
    if (((delta_plane >> j) & 1u) != 0u)
    {
      point[A[j]] ^= (coord_t)(1u << (s - 1));
    }
  }
}

static inline hilbert_state_t state_after_digit(hilbert_state_t st,
                                                uint32_t w,
                                                int k)
{
  const uint32_t mask = mask_bits((uint32_t)k);
  const uint32_t entry = child_entry(w, (uint32_t)k) & mask;

  st.e = affine_apply(entry, st.e, st.d, (uint32_t)k);
  st.d = (st.d + child_dir(w, (uint32_t)k)) % (uint32_t)k;
  return st;
}

void hilbert_affine_decode_domain_stack(const int *m, int n,
                                        hilbert_emit_fn emit, void *ctx)
{
  if (!m || n <= 0 || n > MAX_DIMS || !emit)
    return;

  hilbert_curve_t curve = {0};
  if (!build_active_axes(m, n, &curve) || curve.mmax == 0)
    return;

  const int L = curve.mmax;

  uint32_t w[MAX_LEVELS + 1] = {0};     /* digits: w[1] is least-significant */
  uint32_t plane[MAX_LEVELS + 1] = {0}; /* cached packed planes per level    */
  hilbert_state_t st_stack[MAX_LEVELS + 1];
  coord_t p[MAX_DIMS];

  memset(p, 0, (size_t)n * sizeof(coord_t));
  memset(st_stack, 0, sizeof(st_stack));

  st_stack[L].e = 0u;
  st_stack[L].d = 0u;

  hindex_t index = 0;

  /* Build the full stack for index 0 */
  for (int s = L; s >= 1; --s)
  {
    const int k = curve.k_level[s];
    const int *A = curve.axes_ordered;

    const uint32_t g = gray_code_axis0(w[s], (uint32_t)k);
    const uint32_t new_plane = affine_apply(g, st_stack[s].e, st_stack[s].d, (uint32_t)k);

    plane[s] = new_plane;
    scatter_plane(p, A, k, s, new_plane);

    st_stack[s - 1] = state_after_digit(st_stack[s], w[s], k);
  }

  emit(index++, p, n, ctx);

  /* Enumerate remaining indices by carry + suffix recompute */
  for (;;)
  {
    int s0 = 1;
    while (s0 <= L)
    {
      const uint32_t maxw = mask_bits((uint32_t)curve.k_level[s0]);
      if (w[s0] != maxw)
        break;
      w[s0] = 0u; /* overflow -> reset and carry */
      s0++;
    }
    if (s0 > L)
      break; /* overflow at the top -> finished */

    w[s0]++; /* first non-max digit increments */

    /* Recompute only the suffix s0,s0-1,...,1; higher stack frames stay valid */
    for (int s = s0; s >= 1; --s)
    {
      const int k = curve.k_level[s];
      const int *A = curve.axes_ordered;

      const uint32_t g = gray_code_axis0(w[s], (uint32_t)k);
      const uint32_t new_plane = affine_apply(g, st_stack[s].e, st_stack[s].d, (uint32_t)k);

      const uint32_t delta = new_plane ^ plane[s];
      toggle_scatter_delta(p, A, k, s, delta);

      plane[s] = new_plane;
      st_stack[s - 1] = state_after_digit(st_stack[s], w[s], k);
    }

    emit(index++, p, n, ctx);
  }
}
