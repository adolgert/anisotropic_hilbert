/*
 * refine_pi.c
 *
 * Base (equal-sides) Hilbert encode/decode using the affine state (e, pi)
 * formulation from refine_pi.md, where pi is represented as a rotation index r
 * for the cyclic permutation sigma^{-r}.
 *
 * State:
 *   e : entry mask (bitvector)
 *   r : rotation index (pi = sigma^{-r})
 *
 * Per-level maps:
 *   decode: plane = apply_pi(G(w), r) XOR e
 *   encode: w = G^{-1}(apply_pi_inv(plane XOR e, r))
 *
 * Constraints:
 *   n <= 32, m <= 32, n*m <= 128.
 */

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#define MAX_DIMS 32
#define MAX_BITS_PER_AXIS 32
#define MAX_INDEX_BITS 128

typedef __uint128_t hindex_t;
typedef uint32_t coord_t;

typedef struct {
  uint32_t n;
  uint32_t m;
  uint32_t n_mask;
  uint32_t nm_bits;
} refine_pi_t;

static inline uint32_t mask_bits(uint32_t bits) {
  return (bits >= 32u) ? 0xFFFFFFFFu : ((1u << bits) - 1u);
}

static inline uint32_t rotl_n(uint32_t x, uint32_t r, uint32_t n) {
  if (n == 32u) {
    r &= 31u;
    return (r == 0u) ? x : (uint32_t)((x << r) | (x >> (32u - r)));
  }
  const uint32_t mask = mask_bits(n);
  x &= mask;
  r %= n;
  if (r == 0u) return x;
  return (uint32_t)(((x << r) | (x >> (n - r))) & mask);
}

static inline uint32_t rotr_n(uint32_t x, uint32_t r, uint32_t n) {
  if (n == 32u) {
    r &= 31u;
    return (r == 0u) ? x : (uint32_t)((x >> r) | (x << (32u - r)));
  }
  const uint32_t mask = mask_bits(n);
  x &= mask;
  r %= n;
  if (r == 0u) return x;
  return (uint32_t)(((x >> r) | (x << (n - r))) & mask);
}

static inline uint32_t apply_pi(uint32_t v, uint32_t r, uint32_t n) {
  return rotr_n(v, r, n);
}

static inline uint32_t apply_pi_inv(uint32_t v, uint32_t r, uint32_t n) {
  return rotl_n(v, r, n);
}

static inline uint32_t gray_code(uint32_t x) {
  return x ^ (x >> 1);
}

static inline uint32_t gray_decode(uint32_t g) {
  uint32_t x = g;
  x ^= x >> 1;
  x ^= x >> 2;
  x ^= x >> 4;
  x ^= x >> 8;
  x ^= x >> 16;
  return x;
}

static inline uint32_t trailing_ones(uint32_t x) {
  uint32_t c = 0;
  while ((x & 1u) != 0u) {
    c++;
    x >>= 1;
  }
  return c;
}

static inline uint32_t child_entry(uint32_t w) {
  if (w == 0u) return 0u;
  return gray_code((w - 1u) & ~1u);
}

static inline uint32_t child_dir(uint32_t w, uint32_t n) {
  if (w == 0u) return 0u;
  if ((w & 1u) != 0u) return trailing_ones(w) % n;
  return trailing_ones(w - 1u) % n;
}

bool refine_pi_init(refine_pi_t *hc, uint32_t n, uint32_t m) {
  if (!hc) return false;
  if (n == 0u || n > MAX_DIMS) return false;
  if (m == 0u || m > MAX_BITS_PER_AXIS) return false;
  if ((uint64_t)n * (uint64_t)m > MAX_INDEX_BITS) return false;

  hc->n = n;
  hc->m = m;
  hc->n_mask = mask_bits(n);
  hc->nm_bits = n * m;
  return true;
}

void refine_pi_decode(const refine_pi_t *hc, hindex_t h, coord_t *coords_out) {
  if (!hc || !coords_out) return;

  const uint32_t n = hc->n;
  const uint32_t m = hc->m;
  const uint32_t mask = hc->n_mask;

  for (uint32_t j = 0; j < n; j++) coords_out[j] = 0u;

  uint32_t e = 0u;
  uint32_t r = 1u % n;

  for (uint32_t level = 0; level < m; level++) {
    const uint32_t shift = n * (m - 1u - level);
    const uint32_t w = (uint32_t)((h >> shift) & (hindex_t)mask);

    const uint32_t g = gray_code(w) & mask;
    const uint32_t plane = (apply_pi(g, r, n) ^ e) & mask;

    for (uint32_t j = 0; j < n; j++) {
      coords_out[j] = (coord_t)((coords_out[j] << 1) | ((plane >> j) & 1u));
    }

    const uint32_t e_child = child_entry(w) & mask;
    e = (e ^ apply_pi(e_child, r, n)) & mask;
    const uint32_t r_child = (child_dir(w, n) + 1u) % n;
    r = (r + r_child) % n;
  }
}

hindex_t refine_pi_encode(const refine_pi_t *hc, const coord_t *coords) {
  if (!hc || !coords) return (hindex_t)0;

  const uint32_t n = hc->n;
  const uint32_t m = hc->m;
  const uint32_t mask = hc->n_mask;

  uint32_t e = 0u;
  uint32_t r = 1u % n;
  hindex_t h = 0;

  for (uint32_t level = 0; level < m; level++) {
    const uint32_t bitpos = m - 1u - level;
    uint32_t plane = 0u;
    for (uint32_t j = 0; j < n; j++) {
      plane |= (((uint32_t)((coords[j] >> bitpos) & 1u)) << j);
    }
    plane &= mask;

    const uint32_t temp = plane ^ e;
    const uint32_t g = apply_pi_inv(temp, r, n) & mask;
    const uint32_t w = gray_decode(g) & mask;

    h = (h << n) | (hindex_t)w;

    const uint32_t e_child = child_entry(w) & mask;
    e = (e ^ apply_pi(e_child, r, n)) & mask;
    const uint32_t r_child = (child_dir(w, n) + 1u) % n;
    r = (r + r_child) % n;
  }

  return h;
}

#ifdef REFINE_PI_TEST
#include <stdio.h>

static bool roundtrip_all(const refine_pi_t *hc) {
  const uint32_t nm = hc->nm_bits;
  if (nm > 16u) return true;

  const hindex_t limit = (hindex_t)1 << nm;
  coord_t coords[MAX_DIMS];

  for (hindex_t h = 0; h < limit; h++) {
    refine_pi_decode(hc, h, coords);
    hindex_t back = refine_pi_encode(hc, coords);
    if (back != h) {
      return false;
    }
  }
  return true;
}

int main(void) {
  const struct {
    uint32_t n;
    uint32_t m;
  } cases[] = {
    {1u, 6u},
    {2u, 3u},
    {3u, 2u},
    {4u, 2u},
  };

  for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); i++) {
    refine_pi_t hc;
    if (!refine_pi_init(&hc, cases[i].n, cases[i].m)) {
      fprintf(stderr, "init failed for n=%u m=%u\n", cases[i].n, cases[i].m);
      return 1;
    }
    if (!roundtrip_all(&hc)) {
      fprintf(stderr, "roundtrip failed for n=%u m=%u\n", cases[i].n, cases[i].m);
      return 1;
    }
  }

  printf("refine_pi: ok\n");
  return 0;
}
#endif
