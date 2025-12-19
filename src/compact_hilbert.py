"""
compact_hilbert.py

Hamilton's Compact Hilbert Index algorithm (2008) for domains with unequal side lengths.

This is a faithful implementation of Algorithm 4 from:
  Hamilton & Rau-Chaplin, "Compact Hilbert indices: Space-filling curves for
  domains with unequal side lengths", Information Processing Letters 105 (2008) 155-163.

WARNING: This implementation contains the bug present in the original paper.
The direction parameter `d` is NOT reindexed when the active axis set changes.
This causes discontinuities in the resulting curve for certain anisotropic boxes.

Use anisotropic_hilbert.py for a corrected implementation that guarantees
lattice continuity.

This file exists to demonstrate the bug and provide a baseline for comparison.
"""

from __future__ import annotations

from functools import lru_cache
from typing import Dict, Iterable, List, Sequence, Tuple


def gray_code(i: int) -> int:
    """Binary reflected Gray code: gc(i) = i XOR (i >> 1)."""
    return i ^ (i >> 1)


def gray_decode(g: int) -> int:
    """Inverse of binary reflected Gray code (gc^{-1})."""
    i = 0
    while g:
        i ^= g
        g >>= 1
    return i


def trailing_ones(i: int) -> int:
    """Number of trailing 1-bits in i (Hamilton's tsb)."""
    c = 0
    while i & 1:
        c += 1
        i >>= 1
    return c


def _mask(bits: int) -> int:
    return (1 << bits) - 1 if bits > 0 else 0


def rrotate(x: int, r: int, bits: int) -> int:
    """Rotate-right an unsigned 'bits'-bit word."""
    if bits <= 0:
        return x
    r %= bits
    x &= _mask(bits)
    if r == 0:
        return x
    return ((x >> r) | ((x & ((1 << r) - 1)) << (bits - r))) & _mask(bits)


def lrotate(x: int, r: int, bits: int) -> int:
    """Rotate-left an unsigned 'bits'-bit word."""
    if bits <= 0:
        return x
    r %= bits
    x &= _mask(bits)
    if r == 0:
        return x
    return ((x << r) | (x >> (bits - r))) & _mask(bits)


def T(e: int, d: int, bits: int, b: int) -> int:
    """
    Hamilton T-transform:
      T(e,d)(b) = (b XOR e) rotated-right by (d+1) (mod bits)
    """
    if bits <= 0:
        raise ValueError("bits must be positive")
    return rrotate((b ^ e) & _mask(bits), (d + 1) % bits, bits)


def T_inv(e: int, d: int, bits: int, b: int) -> int:
    """
    Inverse of T(e,d). Since T is (XOR e) then rotate-right, the inverse is:
      rotate-left by (d+1), then XOR e.
    """
    if bits <= 0:
        raise ValueError("bits must be positive")
    return (lrotate(b & _mask(bits), (d + 1) % bits, bits) ^ e) & _mask(bits)


@lru_cache(None)
def e_seq(bits: int, i: int) -> int:
    """
    Hamilton entry-point sequence e(i) for a k=bits dimensional cube.
    Theorem 2.10: e(0)=0; e(i)=gc(2*floor((i-1)/2)) for i>0.
    """
    if i == 0:
        return 0
    return gray_code(2 * ((i - 1) // 2))


@lru_cache(None)
def d_seq(bits: int, i: int) -> int:
    """
    Hamilton intra-subcube direction sequence d(i) for k=bits dimensions.
    Theorem 2.9 / Lemma 2.8:
      d(0)=0
      d(i)=g(i-1) if i even
      d(i)=g(i)   if i odd
    where g(i) = trailing_ones(i) and all indices are reduced mod bits.
    """
    if bits <= 0:
        raise ValueError("bits must be positive")
    if i == 0:
        return 0
    if i & 1:
        return trailing_ones(i) % bits
    return trailing_ones(i - 1) % bits


def _priority_order(m: Sequence[int]) -> List[int]:
    """Axis order used for activation: smaller exponent first; tie by axis id."""
    return sorted(range(len(m)), key=lambda ax: (m[ax], ax))


def active_axes_by_level(m: Sequence[int]) -> Dict[int, List[int]]:
    """
    For levels s=1..mmax, return the ordered list of active axes:
      A_s = { axis j | m_j >= s } ordered by the priority rule.

    Monotonicity: A_s ⊆ A_{s-1}. (More axes activate as s decreases.)
    """
    m = tuple(m)
    if any(mi < 0 for mi in m):
        raise ValueError("All exponents m_j must be >= 0")
    n = len(m)
    mmax = max(m) if n else 0
    order = _priority_order(m)
    return {s: [ax for ax in order if m[ax] >= s] for s in range(1, mmax + 1)}


def index_bit_length(m: Sequence[int]) -> int:
    """Total number of bits in the (variable-width) index. Equals sum(m)."""
    return sum(int(mi) for mi in m)


def encode(point: Sequence[int], m: Sequence[int]) -> int:
    """
    Map an n-D integer lattice point to its compact Hilbert index.

    This implements Hamilton's Algorithm 4 (COMPACTHILBERTINDEX) faithfully,
    INCLUDING THE BUG: the direction parameter `d` is not reindexed when
    the active axis set grows.

    Parameters
    ----------
    point : sequence of ints
        Coordinates (p0,...,p_{n-1}) with 0 <= pj < 2^{m_j}.
    m : sequence of ints
        Exponents (m0,...,m_{n-1}) describing the box size.

    Returns
    -------
    h : int
        Compact Hilbert index in [0, 2^{sum(m)}).
    """
    m = tuple(int(mi) for mi in m)
    point = tuple(int(x) for x in point)
    if len(point) != len(m):
        raise ValueError("point and m must have the same length")
    if any(mi < 0 for mi in m):
        raise ValueError("All exponents m_j must be >= 0")

    n = len(m)
    mmax = max(m) if n else 0
    if mmax == 0:
        return 0

    # bounds check
    for j in range(n):
        if not (0 <= point[j] < (1 << m[j] if m[j] else 1)):
            raise ValueError(f"point[{j}] out of bounds for m[{j}]={m[j]}")

    axes_by_s = active_axes_by_level(m)

    h = 0
    e = 0
    d = 0

    for s in range(mmax, 0, -1):
        A = axes_by_s[s]
        k = len(A)

        # BUG: We mask e and d to k bits, but when k grows, we don't
        # properly reindex d to refer to the same physical axis.
        e &= _mask(k)
        d %= k

        # Pack the s-1 bit across active axes into an integer l (k bits).
        l = 0
        for j, ax in enumerate(A):
            l |= ((point[ax] >> (s - 1)) & 1) << j

        # Hamilton step: transform to standard orientation, Gray-decode to get w.
        l_t = T(e, d, k, l)
        w = gray_decode(l_t)

        # Append this variable-width digit.
        h = (h << k) | w

        # Update orientation using the cube's e(w), d(w).
        e = e ^ lrotate(e_seq(k, w), (d + 1) % k, k)
        d = (d + d_seq(k, w) + 1) % k

        # BUG: NO activation embedding here!
        # When the active set grows (k_{s-1} > k_s), Hamilton's algorithm
        # does NOT reindex d to preserve the physical axis it refers to.
        # This causes discontinuities at activation boundaries.

    return h


def decode(h: int, m: Sequence[int]) -> Tuple[int, ...]:
    """
    Inverse of encode(): map a compact Hilbert index to its n-D lattice point.

    This implements Hamilton's inverse algorithm with the same bug as encode().

    Parameters
    ----------
    h : int
        Compact Hilbert index in [0, 2^{sum(m)}).
    m : sequence of ints
        Exponents (m0,...,m_{n-1}).

    Returns
    -------
    point : tuple[int,...]
        Coordinates (p0,...,p_{n-1}).
    """
    m = tuple(int(mi) for mi in m)
    if any(mi < 0 for mi in m):
        raise ValueError("All exponents m_j must be >= 0")

    n = len(m)
    mmax = max(m) if n else 0
    if mmax == 0:
        return tuple([0] * n)

    M = index_bit_length(m)
    if not (0 <= h < (1 << M)):
        raise ValueError(f"h must be in [0, 2^{M})")

    axes_by_s = active_axes_by_level(m)

    # Segment sizes are k(s) for s=mmax..1
    seg_sizes = [len(axes_by_s[s]) for s in range(mmax, 0, -1)]
    bit_pos = sum(seg_sizes)

    e = 0
    d = 0
    point = [0] * n

    for s in range(mmax, 0, -1):
        A = axes_by_s[s]
        k = len(A)

        bit_pos -= k
        w = (h >> bit_pos) & _mask(k)

        # Hamilton inverse step: Gray-encode w, untransform back to current orientation.
        l = gray_code(w)
        l = T_inv(e, d, k, l)

        # Write the recovered bit into each active axis coordinate.
        for j, ax in enumerate(A):
            point[ax] |= ((l >> j) & 1) << (s - 1)

        # Update orientation (same as encode).
        e = e ^ lrotate(e_seq(k, w), (d + 1) % k, k)
        d = (d + d_seq(k, w) + 1) % k

        # BUG: NO activation embedding here!

    return tuple(point)


def iter_points(m: Sequence[int]) -> Iterable[Tuple[int, ...]]:
    """Iterate all points in curve order (decode 0..2^{sum(m)}-1)."""
    m = tuple(int(mi) for mi in m)
    M = index_bit_length(m)
    for h in range(1 << M):
        yield decode(h, m)


def check_continuity(m: Sequence[int]) -> List[Tuple[int, int, Tuple[int, ...], Tuple[int, ...], int]]:
    """
    Check for discontinuities in the curve.

    Returns a list of (h, h+1, point_h, point_h+1, distance) for all
    pairs where the L1 distance is not 1.
    """
    m = tuple(int(mi) for mi in m)
    M = index_bit_length(m)
    discontinuities = []

    prev = None
    for h in range(1 << M):
        curr = decode(h, m)
        if prev is not None:
            dist = sum(abs(a - b) for a, b in zip(prev, curr))
            if dist != 1:
                discontinuities.append((h - 1, h, prev, curr, dist))
        prev = curr

    return discontinuities


if __name__ == "__main__":
    # Demonstrate the bug with a 4x2 box
    print("Hamilton's Compact Hilbert Index (WITH BUG)")
    print("=" * 50)

    # Test case: 4x2 box (m = [2, 1])
    m = (2, 1)
    print(f"\nBox shape: 2^{m[0]} x 2^{m[1]} = {1 << m[0]} x {1 << m[1]}")
    print(f"Total points: {1 << sum(m)}")
    print()

    print("Curve order:")
    points = list(iter_points(m))
    for h, p in enumerate(points):
        prev_dist = ""
        if h > 0:
            dist = sum(abs(a - b) for a, b in zip(points[h-1], p))
            if dist != 1:
                prev_dist = f"  <-- DISCONTINUITY! L1 distance = {dist}"
            else:
                prev_dist = ""
        print(f"  h={h}: {p}{prev_dist}")

    print()
    discontinuities = check_continuity(m)
    if discontinuities:
        print(f"FOUND {len(discontinuities)} DISCONTINUITY(IES):")
        for h1, h2, p1, p2, dist in discontinuities:
            print(f"  h={h1} -> h={h2}: {p1} -> {p2}, L1 distance = {dist}")
    else:
        print("No discontinuities found (this box might not trigger the bug)")
