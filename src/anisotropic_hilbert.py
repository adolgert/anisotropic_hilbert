"""
anisotropic_hilbert.py

A continuous (lattice-continuous) Hilbert-like space-filling curve on an
axis-aligned dyadic box 2^{m0} × ... × 2^{m_{n-1}}.

This implementation follows the geometric machinery in:
  Chris Hamilton, "Compact Hilbert Indices", Technical Report CS-2006-07 (2006)

Key primitives used exactly as in the report:
  - T-transform:   T(e,d)(b) = (b XOR e) rotated-right by (d+1)        (Lemma 2.?? / Sec 2.1.3)
  - HilbertIndex update: e <- e XOR ( e(w) rotated-left by (d+1) ); d <- d + d(w) + 1 (Algorithm 2)
  - Entry points e(i) and directions d(i) sequences (Theorem 2.10 / Theorem 2.9)

We adapt these to "unequal dimensions" by:
  - Processing levels s = max(m) ... 1
  - At level s, the active axes are those with m_j >= s (monotone activation).
  - The number of active axes k(s) increases only when new dimensions "activate".
  - Hilbert digits are variable-width: k(s) bits at level s.
  - When k increases, we *embed* the current (e,d) into the larger active set by:
        e_new: copy old bits into their new positions; newly activated axes get 0-bit entry
        d_new: reindex d by axis-label (keep the *same physical axis* as the exit direction)

The resulting index space has exactly sum(m_j) bits, and the induced order of
points is a Hamiltonian path on the integer lattice grid: successive indices
map to points with Manhattan distance 1.

Public API:
  - encode(point, m):    point -> integer Hilbert index
  - decode(h, m):        integer Hilbert index -> point
  - iter_points(m):      iterate points in curve order

All coordinates and exponents are non-negative integers.
"""

from __future__ import annotations

from dataclasses import dataclass
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
    """Axis order used for activation embedding: smaller exponent first; tie by axis id."""
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


def embed_state(A_old: List[int], A_new: List[int], e_old: int, d_old: int) -> Tuple[int, int]:
    """
    Embed (e_old,d_old) defined on A_old into a larger active axis list A_new.

    - Bits of e_old are copied into the new positions of the same axes.
    - Newly activated axes get entry-bit 0.
    - d_old is reindexed by axis-label: keep the same *physical* direction axis.
    """
    k_old = len(A_old)
    k_new = len(A_new)
    if k_new < k_old:
        raise ValueError("A_new must be a superset of A_old")

    pos_new = {ax: j for j, ax in enumerate(A_new)}

    e_new = 0
    for j, ax in enumerate(A_old):
        if (e_old >> j) & 1:
            e_new |= 1 << pos_new[ax]

    dir_axis = A_old[d_old]  # axis-label in global coordinates
    d_new = pos_new[dir_axis]
    return e_new, d_new


def index_bit_length(m: Sequence[int]) -> int:
    """Total number of bits in the (variable-width) index. For dyadic boxes this equals sum(m)."""
    return sum(int(mi) for mi in m)


def encode(point: Sequence[int], m: Sequence[int]) -> int:
    """
    Map an n-D integer lattice point to its anisotropic Hilbert index.

    Parameters
    ----------
    point : sequence of ints
        Coordinates (p0,...,p_{n-1}) with 0 <= pj < 2^{m_j}.
    m : sequence of ints
        Exponents (m0,...,m_{n-1}) describing the box size 2^{m0}×...×2^{m_{n-1}}.

    Returns
    -------
    h : int
        Hilbert index in [0, 2^{sum(m)}).

    Notes
    -----
    This is the Hamilton HilbertIndex algorithm adapted to variable-width digits:
    at level s, the digit width is k(s) = |{j: m_j >= s}|.
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

        # Activation embedding to next level if the active set grows.
        if s > 1:
            A_next = axes_by_s[s - 1]
            if len(A_next) > k:
                e, d = embed_state(A, A_next, e, d)

    return h


def decode(h: int, m: Sequence[int]) -> Tuple[int, ...]:
    """
    Inverse of encode(): map an index to its n-D lattice point.

    Parameters
    ----------
    h : int
        Hilbert index in [0, 2^{sum(m)}).
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

        # Update orientation and embed if activation grows.
        e = e ^ lrotate(e_seq(k, w), (d + 1) % k, k)
        d = (d + d_seq(k, w) + 1) % k

        if s > 1:
            A_next = axes_by_s[s - 1]
            if len(A_next) > k:
                e, d = embed_state(A, A_next, e, d)

    return tuple(point)


def iter_points(m: Sequence[int]) -> Iterable[Tuple[int, ...]]:
    """Iterate all points in curve order (decode 0..2^{sum(m)}-1)."""
    m = tuple(int(mi) for mi in m)
    M = index_bit_length(m)
    for h in range(1 << M):
        yield decode(h, m)
