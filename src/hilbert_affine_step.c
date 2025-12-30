/*
 * Enumerate all points in increasing Hilbert index using a stack of affine
 * states per level. This matches the conventions in hilbert_affine.c:
 *  - digits are variable-width (k_level[s] bits) in mixed radix
 *  - affine state is (e,d) with S_{e,d}(x)=rotL(d)x XOR e on k active axes
 *  - axis activation handled by the same (e<<=shift; d+=shift) embedding
 */

typedef void (*hilbert_emit_fn)(const coord_t *p, int n, void *ctx);

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
                                                int k,
                                                int k_next)
{
  const uint32_t mask = mask_bits((uint32_t)k);
  const uint32_t entry = child_entry(w, (uint32_t)k) & mask;

  st.e = affine_apply(entry, st.e, st.d, (uint32_t)k);
  st.d = (st.d + child_dir(w, (uint32_t)k)) % (uint32_t)k;

  if (k_next > k)
  {
    const int shift = k_next - k;
    st.e <<= shift;
    st.d += (uint32_t)shift;
  }
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

  uint32_t w[MAX_LEVELS + 1] = {0};       /* digits: w[1] is least-significant */
  uint32_t plane[MAX_LEVELS + 1] = {0};   /* cached packed planes per level    */
  hilbert_state_t st_stack[MAX_LEVELS + 1];
  coord_t p[MAX_DIMS];

  memset(p, 0, (size_t)n * sizeof(coord_t));
  memset(st_stack, 0, sizeof(st_stack));

  st_stack[L].e = 0u;
  st_stack[L].d = 0u;

  /* Build the full stack for index 0 */
  for (int s = L; s >= 1; --s)
  {
    const int k = curve.k_level[s];
    const int *A = curve.axes_ordered + (n - k);

    const uint32_t g = gray_code_axis0(w[s], (uint32_t)k);
    const uint32_t new_plane = affine_apply(g, st_stack[s].e, st_stack[s].d, (uint32_t)k);

    plane[s] = new_plane;
    scatter_plane(p, A, k, s, new_plane);

    st_stack[s - 1] = state_after_digit(st_stack[s], w[s], k, curve.k_level[s - 1]);
  }

  emit(p, n, ctx);

  /* Enumerate remaining indices by carry + suffix recompute */
  for (;;)
  {
    int s0 = 1;
    while (s0 <= L)
    {
      const uint32_t maxw = mask_bits((uint32_t)curve.k_level[s0]);
      if (w[s0] != maxw)
        break;
      w[s0] = 0u;  /* overflow -> reset and carry */
      s0++;
    }
    if (s0 > L)
      break; /* overflow at the top -> finished */

    w[s0]++; /* first non-max digit increments */

    /* Recompute only the suffix s0,s0-1,...,1; higher stack frames stay valid */
    for (int s = s0; s >= 1; --s)
    {
      const int k = curve.k_level[s];
      const int *A = curve.axes_ordered + (n - k);

      const uint32_t g = gray_code_axis0(w[s], (uint32_t)k);
      const uint32_t new_plane = affine_apply(g, st_stack[s].e, st_stack[s].d, (uint32_t)k);

      const uint32_t delta = new_plane ^ plane[s];
      toggle_scatter_delta(p, A, k, s, delta);

      plane[s] = new_plane;
      st_stack[s - 1] = state_after_digit(st_stack[s], w[s], k, curve.k_level[s - 1]);
    }

    emit(p, n, ctx);
  }
}
