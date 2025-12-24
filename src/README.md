# src/ Directory Overview

This directory contains implementations of Hilbert space-filling curves in C and Python, including both **isotropic** (equal-sides, hypercube) and **anisotropic** (unequal-sides, compact) variants.

---

## C Files

### Overview

| File | Type | Purpose |
|------|------|---------|
| `isotropic_hilbert.c` | Isotropic | Standard equal-sides hypercube |
| `refine_pi.c` | Isotropic | Alternative state representation using permutation index |
| `anisotropic_hilbert.c` | Anisotropic | Variable side lengths (compact Hilbert) |
| `hilbert_affine.c` | Anisotropic | Same goal, different affine-map formulation |
| `hilbert_neighbor.c` | Anisotropic | Efficient neighbor index computation |
| `hilbert_skip2.c` | Anisotropic | Skip-2 iteration (compute h+2 without h+1's point) |

---

### Isotropic vs Anisotropic

**Isotropic (equal sides):**
- Grid is `2^m × 2^m × ... × 2^m` (same `m` for all axes)
- All `n` axes are active at every level
- Fixed digit width of `n` bits per level
- Files: `isotropic_hilbert.c`, `refine_pi.c`

**Anisotropic (unequal sides):**
- Grid is `2^{m[0]} × 2^{m[1]} × ... × 2^{m[n-1]}` (different `m[i]`)
- Axes "drop out" as levels go below their resolution
- Variable digit width `k` (number of active axes at each level)
- Requires axis ordering by priority `(m[j], j)` and state embedding when `k` changes
- Files: `anisotropic_hilbert.c`, `hilbert_affine.c`, `hilbert_neighbor.c`, `hilbert_skip2.c`

---

### Decomposition Approaches

**1. T-transform (isotropic_hilbert.c:98-106)**
```
T(e,d)(b)    = rotR(d+1)(b XOR e)
T_inv(e,d)(b) = rotL(d+1)(b) XOR e
```
State is `(e, d)` where `e` is entry mask, `d` is direction index.

**2. Affine S-transform (hilbert_affine.c:101-109)**
```
S_{e,d}(x)    = rotL(d+1)(x) XOR e
S^{-1}(y)     = rotR(d+1)(y XOR e)
```
Essentially the inverse of the T-transform; different convention for encode vs decode.

**3. Pi (permutation) formulation (refine_pi.c:66-71)**
```
apply_pi(v, r, n)     = rotR(v, r, n)  // pi = sigma^{-r}
apply_pi_inv(v, r, n) = rotL(v, r, n)
```
State is `(e, r)` where `r` is a rotation index. This factors the affine map into a permutation (rotation) plus XOR.

---

### Common Elements Across All C Files

1. **Gray code** for hypercube adjacency (`gray_code`, `gray_decode`)
2. **Hamilton's sequences** for state updates:
   - `child_entry(w)` = `gray_code(2 * floor((w-1)/2))`
   - `child_dir(w, k)` = based on trailing ones in `w` or `w-1`
3. **128-bit index type** (`__uint128_t hindex_t`)
4. **MAX_DIMS = 32**
5. **MSB-first level processing** (high bits correspond to coarse subdivision)
6. **Bit rotation primitives** (`rotl_n`, `rotr_n`)

---

### Anisotropic-Specific Machinery

All anisotropic C files share this additional structure:

1. **Axis ordering** (`sort_axes_by_exp`): sorts axes by `(m[j], j)` to determine activation order
2. **Active axis tracking** (`get_active_axes`): determines which axes are active at level `s`
3. **State embedding** (`embed_state`): when transitioning from level `s` to `s-1` and `k` increases, the `(e, d)` state must be remapped to the new larger active set

---

### Special-Purpose C Files

**`hilbert_neighbor.c`** — Caches full decode state to efficiently compute neighbor indices:
- Stores state `(e, d)` at entry to each level
- To get `h` for `p ± e_axis`, finds the highest affected level, reuses cached state above it, recomputes only from that level down
- Optimization: avoids full re-encode for neighbor lookups

**`hilbert_skip2.c`** — Computes `p₂ = H(h+2)` from `p₀` without reconstructing `p₁`:
- Key insight: state updates are cheap, point reconstruction is expensive
- Simulates two state transitions, tracks which axes change and by how much
- Can detect cancellations where `p₂ = p₀` (two opposite steps on same axis)
- Useful for parallel iteration where workers can initialize at arbitrary `h`

---

### C File Summary Table

| File | State | Axes | Digit Width | Special Feature |
|------|-------|------|-------------|-----------------|
| `isotropic_hilbert.c` | (e, d) | All n | n bits | Clean reference implementation |
| `refine_pi.c` | (e, r) | All n | n bits | Permutation-based state |
| `anisotropic_hilbert.c` | (e, d) | Variable k | k bits | Hamilton's compact formulation |
| `hilbert_affine.c` | (e, d) | Variable k | k bits | Affine S-transform formulation |
| `hilbert_neighbor.c` | Cached (e, d) per level | Variable k | k bits | Efficient neighbor computation |
| `hilbert_skip2.c` | (e, d) per level | Variable k | k bits | Skip-2 without intermediate point |

---

## Python Files

### Overview

| File | Category | Purpose |
|------|----------|---------|
| `anisotropic_hilbert.py` | Core | Pure Python anisotropic Hilbert (corrected algorithm) |
| `compact_hilbert.py` | Core | Hamilton's original algorithm WITH the bug (for comparison) |
| `anisotropic_hilbert_c.py` | Wrapper | ctypes wrapper for C implementation |
| `continuous_anisotropic_hilbert.py` | Extension | Continuous curve on [0,1] → R^n |
| `demo.py` | Demo | Demonstrates discrete anisotropic Hilbert |
| `demo_continuous.py` | Demo | Demonstrates continuous extension |
| `test_anisotropic_hilbert.py` | Test | Unit tests for discrete implementations |
| `test_continuous_anisotropic_hilbert.py` | Test | Unit tests for continuous extension |
| `fix_math_delimiters.py` | Utility | Markdown math delimiter converter (unrelated) |

---

### Core Python Implementations

**`anisotropic_hilbert.py`** — The primary pure-Python implementation:
- Implements Hamilton's compact Hilbert index algorithm with a **critical bug fix**
- The fix: when axes activate (k increases), the direction index `d` must be **reindexed** to refer to the same physical axis in the new larger active set
- Provides `encode(point, m)`, `decode(h, m)`, `iter_points(m)`
- Uses the T-transform: `T(e,d)(b) = rotR(d+1)(b XOR e)`
- State is `(e, d)` with `embed_state()` for activation transitions

**`compact_hilbert.py`** — Hamilton's original algorithm **with the bug preserved**:
- Faithful implementation of Algorithm 4 from Hamilton & Rau-Chaplin (2008)
- **Does NOT reindex `d` when axes activate** — this causes discontinuities
- Includes `check_continuity(m)` to demonstrate the bug
- Exists for comparison and to demonstrate what goes wrong without the fix

**`anisotropic_hilbert_c.py`** — ctypes wrapper for the C library:
- Provides the same API as `anisotropic_hilbert.py`
- Loads `libanisotropic_hilbert.dylib` (macOS) or `.so` (Linux)
- Supports both 64-bit and 128-bit indices (hi/lo split for ctypes)
- Includes `decode_batch()` for efficient bulk decoding

---

### Continuous Extension

**`continuous_anisotropic_hilbert.py`** — Extends the discrete curve to a true continuous space-filling curve:

The key idea:
- For fixed "shape offsets" `c = (c0, ..., c_{n-1})`, consider boxes `m^(k) = (k+c0, ..., k+c_{n-1})`
- At depth `k`, the lattice has `2^{k+ci}` points along axis `i`
- Scaling by `2^{-k}` gives a fixed target box `B_c = [0, 2^{c0}] × ... × [0, 2^{c_{n-1}}]`
- For `t ∈ [0,1)`, define `h_k(t) = floor(t × 2^{sum(m^(k))})`
- The scaled points `x_k(t) = (decode(h_k(t), m^(k)) + 0.5) / 2^k` form a Cauchy sequence
- The limit `H_c(t)` is a continuous space-filling curve on `B_c`

Provides:
- `eval_point(t, offsets, depth, ...)` — finite-depth approximation of `H_c(t)`
- `approx_inverse(x, offsets, depth, ...)` — returns parameter interval containing `x`
- `refinement_consistency_holds(...)` — verifies `p_{k+1} >> 1 == p_k`

---

### Demos

**`demo.py`** — Simple demonstration of discrete anisotropic curves:
```python
show((2,1))    # 4×2 box
show((3,1))    # 8×2 box
show((2,2,1))  # 4×4×2 box
```

**`demo_continuous.py`** — Demonstrates the continuous extension:
- Shows how `eval_point(t, offsets, depth)` converges as depth increases
- Examples with and without unit-cube normalization

---

### Tests

**`test_anisotropic_hilbert.py`** — Comprehensive tests for the discrete curve:
- **Lattice continuity**: Manhattan distance between consecutive points is exactly 1
- **Bijection**: `encode(decode(h)) == h` and `decode(encode(p)) == p`
- **Bounds/uniqueness**: all points within bounds and unique
- Exhaustive tests for 2D (up to 32×32), 3D (up to 16³), 4D (up to 8⁴)
- Optional `SLOW_TESTS=1` for 5D exhaustive
- Optional `GLACIAL_TESTS=1` for random large shapes (2D-7D, up to 268M points)
- Automatically uses C implementation if available

**`test_continuous_anisotropic_hilbert.py`** — Tests for the continuous extension:
- **Refinement consistency**: `p_{k+1} >> 1 == p_k` (nested cell property)
- **Scaled lattice continuity**: step size is exactly `2^{-k}` at depth `k`
- **Approx-inverse correctness**: round-trip through `eval_point` and `approx_inverse`

---

### Python File Relationships

```
anisotropic_hilbert.py  ←─── anisotropic_hilbert_c.py (wraps C for speed)
        │
        ├─── continuous_anisotropic_hilbert.py (extends to continuous)
        │
        └─── compact_hilbert.py (buggy version for comparison)

test_anisotropic_hilbert.py ─── tests both .py and _c.py implementations
test_continuous_anisotropic_hilbert.py ─── tests continuous extension
```

---

### Key Differences: Python vs C

| Aspect | Python | C |
|--------|--------|---|
| Index type | Arbitrary precision `int` | `__uint128_t` (max 128 bits) |
| Max dimensions | Unlimited (practical ~32) | `MAX_DIMS = 32` |
| Performance | Slower, but readable | Fast, optimized |
| Special features | Continuous extension | Neighbor computation, skip-2 |

---

### The Hamilton Bug

Both `compact_hilbert.py` and the corrected `anisotropic_hilbert.py` implement Hamilton's Algorithm 4 for compact Hilbert indices. The difference:

**The bug** (in the original paper and `compact_hilbert.py`):
- When the active axis set grows (`k_{s-1} > k_s`), the direction index `d` is simply taken `mod k_{s-1}`
- This causes `d` to potentially refer to a **different physical axis** than intended
- Result: discontinuities in the curve at activation boundaries

**The fix** (in `anisotropic_hilbert.py`):
- When axes activate, call `embed_state()` to **reindex** both `e` and `d`
- The direction `d` is converted: find which physical axis it referred to, then find that axis's new position in the larger active set
- Result: guaranteed lattice continuity (Manhattan distance 1 between consecutive points)

To see the bug in action:
```bash
python compact_hilbert.py  # Shows discontinuities in a 4×2 box
```

---

## Building

To build the C library:
```bash
make
```

This produces `libanisotropic_hilbert.dylib` (macOS) or `.so` (Linux), which is automatically loaded by `anisotropic_hilbert_c.py`.

## Running Tests

```bash
# Run all tests (uses C implementation if available)
python -m unittest discover -v

# Run with pure Python only
# (rename or remove the .dylib/.so file)

# Enable slow/glacial tests
SLOW_TESTS=1 python -m unittest -v
GLACIAL_TESTS=1 python -m unittest -v
```
