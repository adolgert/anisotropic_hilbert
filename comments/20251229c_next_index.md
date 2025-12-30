The cleanest way to enumerate **all** `h -> point` pairs (in increasing Hilbert index) without re-decoding from scratch is to turn your decoder into a **streaming decoder**:

* keep the per-level **digit** `w[s]` (your mixed-radix “Hilbert digit” at level `s`)
* keep the per-level **affine state** `st_stack[s] = (e,d)` (state *before* consuming digit `w[s]`)
* keep the per-level **plane bits** `plane[s]` (the post-transform Gray-coded plane at that level)
* keep the current **point** `p[]`
* on `h++`, do a mixed-radix carry on `w[1], w[2], ...` and then recompute **only the suffix** of levels affected by the carry.

That is exactly the direction of your `hilbert_affine_step.c`, and it matches the way `hilbert_affine_decode()` is written.

`hilbert_neighbor.c` is solving a different problem (random neighbor queries); for a full sequential scan it ends up doing much more work than necessary.

## Why the “stack of affine states” method is the right fit for `hilbert_affine.c`

In `hilbert_affine_decode()` each level does:

1. read digit `w`
2. `g = gray_code_axis0(w,k)`
3. `plane = affine_apply(g, e, d, k)`
4. scatter that plane into bit `(s-1)` of the coordinates
5. update `(e,d)` to the child state, plus “embed” if `k_next > k`

So if you are enumerating indices in order, the only levels that change when you increment are the low levels where a carry happens. Everything above the carry is unchanged, so their affine states and planes remain valid.

This gives an *amortized constant* update:

* expected number of changed digits is small (for uniform radix `b`, it’s `b/(b-1)`; in 3D `b=8` so ≈ `1.142` digits per step).
* per changed level you touch only `k` active axes (and with your `sum(m) <= 128`, average `k` is rarely large).

## What I would implement in `hilbert_affine.c`

### Option A: a “foreach” enumerator (minimal API, easiest to drop in)

This is basically your `hilbert_affine_step.c`, but I’d make two changes for practicality:

1. emit the **index** as well as the point (since you want index↔point pairs)
2. handle the degenerate `sum(m)==0` case by emitting the single point `{0,...,0}` once

Here is a drop-in style implementation that uses your existing helpers (`build_active_axes`, `scatter_plane`, `gray_code_axis0`, `affine_apply`, `child_entry`, `child_dir`, `mask_bits`, etc.):

```c
typedef void (*hilbert_emit_idx_fn)(hindex_t h, const coord_t *p, int n, void *ctx);

static inline void toggle_scatter_delta(coord_t *point,
                                        const int *A, int k, int s,
                                        uint32_t delta_plane)
{
  for (int j = 0; j < k; j++)
  {
    if (((delta_plane >> j) & 1u) != 0u)
      point[A[j]] ^= (coord_t)(1u << (s - 1));
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

void hilbert_affine_foreach(const int *m, int n, hilbert_emit_idx_fn emit, void *ctx)
{
  if (!m || n <= 0 || n > MAX_DIMS || !emit)
    return;

  hilbert_curve_t curve = {0};
  if (!build_active_axes(m, n, &curve))
    return;

  /* Degenerate domain: exactly one point */
  if (curve.total_bits == 0)
  {
    coord_t p0[MAX_DIMS] = {0};
    emit((hindex_t)0, p0, n, ctx);
    return;
  }

  const int L = curve.mmax;

  uint32_t w[MAX_LEVELS + 1] = {0};       /* digits: w[1] least significant */
  uint32_t plane[MAX_LEVELS + 1] = {0};   /* cached planes per level        */
  hilbert_state_t st_stack[MAX_LEVELS + 1];
  coord_t p[MAX_DIMS];

  memset(p, 0, (size_t)n * sizeof(coord_t));
  memset(st_stack, 0, sizeof(st_stack));

  st_stack[L].e = 0u;
  st_stack[L].d = 0u;

  /* Build full stack + point for h=0 */
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

  hindex_t h = 0;
  emit(h, p, n, ctx);

  /* Enumerate remaining indices by carry + suffix recompute */
  for (;;)
  {
    int s0 = 1;
    while (s0 <= L)
    {
      const uint32_t maxw = mask_bits((uint32_t)curve.k_level[s0]);
      if (w[s0] != maxw)
        break;
      w[s0] = 0u;
      s0++;
    }
    if (s0 > L)
      break; /* overflow => done */

    w[s0]++; /* increment first non-max digit */
    h++;     /* packed Hilbert index increments by 1 */

    /* Recompute only the suffix s0,s0-1,...,1 */
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

    emit(h, p, n, ctx);
  }
}
```

That gives you a single pass that emits every `(h, point)` in strictly increasing Hilbert index order, without re-running a full decode per point.

### Option B: a reusable iterator object (more flexible, still compact)

If you want something you can pause/resume, split into chunks, or parallelize, wrap the same machinery in:

* `hilbert_affine_iter_init(&it, m, n)`  (build curve, set to `h=0`, build stacks)
* `hilbert_affine_iter_next(&it, &h, point)`  (returns current, advances to next)
* optional: `hilbert_affine_iter_seek(&it, h0)`  (decode once to build stacks for a starting index)

That iterator is basically your `hilbert_neighbor_init()` idea, but for **sequential scan** you don’t need neighbor logic—just “carry + suffix recompute”.

## Why I would not base a full scan on `hilbert_neighbor.c`

`hilbert_neighbor.c` is useful when you ask: “given the current point, what is the Hilbert index of the neighbor at `axis += ±1`?” That’s a different query pattern.

For full enumeration:

* you already know the next index (`h+1`)
* you do **not** want to solve an inverse problem each step (“which neighbor is next?”)
* you want the minimal amount of recomputation, which is exactly “carry + recompute suffix”

So the neighbor approach is structurally heavier than necessary for this task.

## Two small refinements I would consider (micro-optimizations)

1. **Toggle only set bits** in `delta_plane` (instead of scanning `j=0..k-1`), if you ever have large `k`:

   ```c
   while (delta_plane)
   {
     uint32_t j = (uint32_t)__builtin_ctz(delta_plane);
     point[A[j]] ^= (coord_t)(1u << (s - 1));
     delta_plane &= delta_plane - 1;
   }
   ```

   This tends to be faster when `delta_plane` is sparse, but for small `k` your current loop is fine.

2. If you want the **packed `h` as (hi,lo)** every time, emit it as two `uint64_t` values to avoid repeated shifts in user code:

   ```c
   uint64_t lo = (uint64_t)h;
   uint64_t hi = (uint64_t)(h >> 64);
   ```

## Bottom line recommendation

Use the `hilbert_affine_step.c` approach, not the neighbor approach:

* it matches your affine formulation exactly
* it gives amortized O(1) work per emitted point
* it’s easy to keep consistent with `hilbert_affine_decode()` because it is literally the same per-level computation, just cached and updated on carry

If you want, I can rewrite your `hilbert_affine_step.c` as an iterator struct with a `next()` function that plugs directly into your existing `hilbert_affine.c` style (same naming, same types, no duplicated logic), including an optional `seek(h0)` that builds the per-level caches for chunked/parallel enumeration.
