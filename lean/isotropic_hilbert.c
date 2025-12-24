// Isotropic (equal-sides) Hilbert encode/decode for n ≤ 32 dimensions.
//
// This is a compact implementation of the affine/Gray-code formulation described in
// `refine_affine.md`, specialized to the isotropic (hypercube) case:
// - each level consumes/produces an n-bit "digit" w
// - Gray code provides hypercube adjacency
// - an orientation state (e,d) is updated per level
//
// Conventions match the Lean skeleton in `AnisoHilbert/Representation.lean`:
//   T(e,d)(b)   = rotR(d+1) (b XOR e)
//   Tinv(e,d)(b)= (rotL(d+1) b) XOR e
//
// Axis j corresponds to bit j (LSB = axis 0).

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#define MAX_DIMS 32

typedef __uint128_t hindex_t;
typedef uint32_t coord_t;

typedef struct {
  uint32_t n;       // dimensions, 1..MAX_DIMS
  uint32_t m;       // bits per axis, 1..32
  uint32_t n_mask;  // low n bits set (or all ones for n==32)
  uint32_t nm_bits; // n*m, must be <= 128 for hindex_t
} isotropic_hilbert_t;

static inline uint32_t hilbert_mask_n(uint32_t n) {
  return (n >= 32u) ? 0xFFFFFFFFu : ((1u << n) - 1u);
}

static inline uint32_t rotl_n(uint32_t x, uint32_t r, uint32_t n) {
  if (n == 32u) {
    r &= 31u;
    return (r == 0u) ? x : (uint32_t)((x << r) | (x >> (32u - r)));
  }
  const uint32_t mask = hilbert_mask_n(n);
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
  const uint32_t mask = hilbert_mask_n(n);
  x &= mask;
  r %= n;
  if (r == 0u) return x;
  return (uint32_t)(((x >> r) | (x << (n - r))) & mask);
}

static inline uint32_t gray_u32(uint32_t x) {
  return x ^ (x >> 1);
}

static inline uint32_t gray_inv_u32(uint32_t g) {
  uint32_t x = g;
  // Standard Gray inverse via repeated XOR with shifted self.
  x ^= x >> 1;
  x ^= x >> 2;
  x ^= x >> 4;
  x ^= x >> 8;
  x ^= x >> 16;
  return x;
}

// Trailing set bits (tsb): number of consecutive 1 bits from the LSB.
static inline uint32_t tsb_u32(uint32_t x) {
  uint32_t c = 0;
  while ((x & 1u) != 0u) {
    c++;
    x >>= 1;
  }
  return c;
}

// Hamilton Theorem 2.10 (entry corner), specialized to isotropic k=n.
static inline uint32_t child_entry_u32(uint32_t w) {
  if (w == 0u) return 0u;
  const uint32_t j = (w - 1u) & ~1u; // 2 * floor((w-1)/2)
  return gray_u32(j);
}

// Hamilton Theorem 2.9 (direction), specialized to isotropic k=n.
static inline uint32_t child_dir_u32(uint32_t w, uint32_t n) {
  if (w == 0u) return 0u;
  if ((w & 1u) == 0u) return tsb_u32(w - 1u) % n; // w even
  return tsb_u32(w) % n;                           // w odd
}

// T-transform: XOR by e, then rotate right by (d+1).
static inline uint32_t T_u32(uint32_t b, uint32_t e, uint32_t d, uint32_t n) {
  return rotr_n((b ^ e), d + 1u, n);
}

// Inverse of T: rotate left by (d+1), then XOR by e.
static inline uint32_t Tinv_u32(uint32_t b, uint32_t e, uint32_t d, uint32_t n) {
  return (rotl_n(b, d + 1u, n) ^ e);
}

bool isotropic_hilbert_init(isotropic_hilbert_t *hc, uint32_t n, uint32_t m) {
  if (!hc) return false;
  if (n == 0u || n > MAX_DIMS) return false;
  if (m == 0u || m > 32u) return false;

  const uint32_t nm = n * m;
  if (nm > 128u) return false;

  hc->n = n;
  hc->m = m;
  hc->n_mask = hilbert_mask_n(n);
  hc->nm_bits = nm;
  return true;
}

// Decode: Hilbert index -> coordinates (coords_out has length >= hc->n).
void isotropic_hilbert_decode(const isotropic_hilbert_t *hc, hindex_t h, coord_t *coords_out) {
  if (!hc || !coords_out) return;

  const uint32_t n = hc->n;
  const uint32_t m = hc->m;
  const uint32_t mask = hc->n_mask;

  uint32_t e = 0u; // entry mask
  uint32_t d = 0u; // direction index (interpreted mod n)

  for (uint32_t j = 0; j < n; j++) coords_out[j] = 0u;

  // Process digits MSB-first (level 0 is the top cube).
  for (uint32_t level = 0; level < m; level++) {
    const uint32_t shift = n * (m - 1u - level);
    const uint32_t w = (uint32_t)((h >> shift) & (hindex_t)mask);

    const uint32_t g = gray_u32(w) & mask;
    const uint32_t plane = Tinv_u32(g, e, d, n) & mask;

    // Scatter plane bits into coordinates, MSB-first: coords[j] = (coords[j] << 1) | plane[j].
    for (uint32_t j = 0; j < n; j++) {
      coords_out[j] = (coord_t)((coords_out[j] << 1) | ((plane >> j) & 1u));
    }

    // State update: (e,d) <- (e,d) · μ(w)
    const uint32_t ce = child_entry_u32(w) & mask;
    e = (e ^ rotl_n(ce, d + 1u, n)) & mask;
    d = (d + child_dir_u32(w, n) + 1u) % n;
  }
}

// Encode: coordinates -> Hilbert index (coords has length >= hc->n).
hindex_t isotropic_hilbert_encode(const isotropic_hilbert_t *hc, const coord_t *coords) {
  if (!hc || !coords) return (hindex_t)0;

  const uint32_t n = hc->n;
  const uint32_t m = hc->m;
  const uint32_t mask = hc->n_mask;

  uint32_t e = 0u;
  uint32_t d = 0u;
  hindex_t h = 0;

  for (uint32_t level = 0; level < m; level++) {
    // Gather this plane's label ℓ (MSB-first plane order).
    const uint32_t bitpos = m - 1u - level;
    uint32_t plane = 0u;
    for (uint32_t j = 0; j < n; j++) {
      plane |= (((uint32_t)((coords[j] >> bitpos) & 1u)) << j);
    }
    plane &= mask;

    // w = gc^{-1}( T(e,d)(plane) )
    const uint32_t planeT = T_u32(plane, e, d, n) & mask;
    const uint32_t w = gray_inv_u32(planeT) & mask;

    h = (h << n) | (hindex_t)w;

    // State update by child tables.
    const uint32_t ce = child_entry_u32(w) & mask;
    e = (e ^ rotl_n(ce, d + 1u, n)) & mask;
    d = (d + child_dir_u32(w, n) + 1u) % n;
  }

  return h;
}

