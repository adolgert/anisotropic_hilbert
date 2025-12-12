"""continuous_anisotropic_hilbert.py

Continuous extension of the anisotropic (unequal-dimension) Hilbert-like
lattice curve implemented in `anisotropic_hilbert.py`.

Concept
-------
For a fixed "shape offset" vector c = (c0,...,c_{n-1}) with ci >= 0,
consider the sequence of dyadic boxes

    m^(k) = (k + c0, ..., k + c_{n-1})      for k = 0,1,2,...

The integer lattice in that box has side lengths 2^{k+ci} in axis i.
When scaled by 2^{-k}, this becomes a fixed axis-aligned box

    B_c = [0,2^{c0}] x ... x [0,2^{c_{n-1}}].

At each k, `decode(h, m^(k))` enumerates the lattice points by a
unit-step Hamiltonian path (Manhattan adjacency = 1). Scaling by 2^{-k}
turns it into a polygonal approximation with step length 2^{-k}.

For t in [0,1), define h_k(t) = floor(t * 2^{sum(m^(k))}). Then the
scaled points

    x_k(t) = (decode(h_k(t), m^(k)) + 0.5) / 2^k

form a Cauchy sequence (except for the usual dyadic-expansion ambiguity at
certain t), hence converge to a point H_c(t) in B_c. This gives a true
continuous space-filling curve on B_c.

The +0.5 chooses cell centers; it is optional but avoids boundary bias.

Public API
----------
- eval_point(t, offsets, depth, ...): finite-depth approximation of H_c(t)
- approx_inverse(x, offsets, depth, ...): return the parameter interval
  whose depth-approximation cell contains x

The implementation reuses `encode/decode` from anisotropic_hilbert.

"""

from __future__ import annotations

import os
import math
from dataclasses import dataclass
import sys
from typing import Iterable, Optional, Sequence, Tuple

# Allow importing when this file is executed or imported from outside its directory.
_THIS_DIR = os.path.dirname(os.path.abspath(__file__))
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

from anisotropic_hilbert import decode, encode


def offsets_box_lengths(offsets: Sequence[int]) -> Tuple[float, ...]:
    """Return the canonical dyadic box lengths (2^{c_i})."""
    return tuple(float(1 << int(c)) for c in offsets)


def m_from_offsets(depth: int, offsets: Sequence[int]) -> Tuple[int, ...]:
    """m^(depth) = depth + offsets."""
    if depth < 0:
        raise ValueError("depth must be >= 0")
    offs = tuple(int(c) for c in offsets)
    if any(c < 0 for c in offs):
        raise ValueError("offsets must be >= 0")
    return tuple(depth + c for c in offs)


def _clamp_int(x: int, lo: int, hi: int) -> int:
    return lo if x < lo else hi if x > hi else x


def _h_from_t(t: float, M: int) -> int:
    """Map t in [0,1] to an integer h in [0,2^M-1] by floor(t*2^M)."""
    if not (0.0 <= t <= 1.0):
        raise ValueError("t must be in [0,1]")
    if M < 0:
        raise ValueError("M must be >= 0")
    if M == 0:
        return 0
    # Treat t==1 as the last index.
    if t >= 1.0:
        return (1 << M) - 1
    h = int(math.floor(t * (1 << M)))
    return _clamp_int(h, 0, (1 << M) - 1)


def eval_point(
    t: float,
    offsets: Sequence[int],
    depth: int,
    *,
    center: bool = True,
    normalize_to_unit: bool = False,
    lengths: Optional[Sequence[float]] = None,
) -> Tuple[float, ...]:
    """Finite-depth approximation of the continuous anisotropic Hilbert curve.

    Parameters
    ----------
    t:
        Curve parameter in [0,1].
    offsets:
        Nonnegative integer exponents c_i determining the target dyadic box
        B_c = ∏ [0,2^{c_i}].
    depth:
        Refinement depth k (extra bits beyond offsets). Larger depth gives
        finer approximation.
    center:
        If True, return the center of the visited lattice cell at this depth.
        If False, return the lattice point itself scaled.
    normalize_to_unit:
        If True, map into the unit cube [0,1]^n instead of B_c.
    lengths:
        Optional physical side lengths L_i. If provided, the output is
        affinely scaled from B_c to ∏[0,L_i]. (Continuity is preserved.)

    Returns
    -------
    point:
        n-tuple of floats.
    """
    offs = tuple(int(c) for c in offsets)
    m = m_from_offsets(depth, offs)
    M = sum(m)
    h = _h_from_t(t, M)
    p = decode(h, m)

    # Base scale: B_c has units of 2^{-depth}.
    denom = float(1 << depth) if depth >= 0 else 1.0

    if center:
        x = tuple((pi + 0.5) / denom for pi in p)
    else:
        x = tuple(pi / denom for pi in p)

    if normalize_to_unit:
        # Divide by 2^{c_i}
        x = tuple(xi / float(1 << ci) for xi, ci in zip(x, offs))

    if lengths is not None:
        L = tuple(float(v) for v in lengths)
        if len(L) != len(x):
            raise ValueError("lengths must have the same length as offsets")
        base = offsets_box_lengths(offs)
        x = tuple(xi * (Li / bi) for xi, Li, bi in zip(x, L, base))

    return x


@dataclass(frozen=True)
class ParamInterval:
    """A parameter interval [a,b) at a given depth, plus the associated index."""

    a: float
    b: float
    h: int
    M: int


def approx_inverse(
    x: Sequence[float],
    offsets: Sequence[int],
    depth: int,
    *,
    normalize_from_unit: bool = False,
    lengths: Optional[Sequence[float]] = None,
) -> ParamInterval:
    """Approximate inverse (finite-depth): return the parameter interval
    whose depth-approximation cell contains x.

    This is *not* a true inverse of the limiting continuous curve (the
    continuous curve is not injective), but it is the natural inverse at
    fixed depth.

    Parameters
    ----------
    x:
        Point in B_c (or in ∏[0,L_i] if lengths is given).
    offsets, depth:
        As in eval_point.
    normalize_from_unit:
        If True, interpret x as belonging to [0,1]^n before scaling to B_c.
    lengths:
        If provided, interpret x as belonging to ∏[0,L_i] and scale back
        into B_c before quantization.

    Returns
    -------
    ParamInterval:
        interval [a,b) at this depth (with denominator 2^M).
    """
    offs = tuple(int(c) for c in offsets)
    m = m_from_offsets(depth, offs)
    M = sum(m)

    xx = tuple(float(v) for v in x)
    if len(xx) != len(offs):
        raise ValueError("x and offsets must have same length")

    # Map x into B_c coordinates.
    if lengths is not None:
        L = tuple(float(v) for v in lengths)
        if len(L) != len(xx):
            raise ValueError("lengths must have the same length as offsets")
        base = offsets_box_lengths(offs)
        xx = tuple(xi * (bi / Li) for xi, Li, bi in zip(xx, L, base))

    if normalize_from_unit:
        xx = tuple(xi * float(1 << ci) for xi, ci in zip(xx, offs))

    # Quantize to the depth grid in B_c.
    # Each axis i has 2^{depth+ci} cells along it; in B_c units, cell size is 2^{-depth}.
    denom = float(1 << depth)
    p = []
    for xi, ci in zip(xx, offs):
        # Clamp to [0, 2^{ci})
        max_x = float(1 << ci)
        xi = 0.0 if xi < 0.0 else (max_x - (1.0 / denom)) if xi >= max_x else xi
        pi = int(math.floor(xi * denom))
        # Convert to index-space coordinate (0..2^{depth+ci}-1)
        pi = _clamp_int(pi, 0, (1 << (depth + ci)) - 1)
        p.append(pi)

    h = encode(tuple(p), m)
    a = h / float(1 << M)
    b = (h + 1) / float(1 << M)
    return ParamInterval(a=a, b=b, h=h, M=M)


def refinement_consistency_holds(offsets: Sequence[int], depth: int, t: float) -> bool:
    """Diagnostic: check p_{k+1} >> 1 == p_k for the given t and offsets."""
    offs = tuple(int(c) for c in offsets)
    m1 = m_from_offsets(depth, offs)
    m2 = m_from_offsets(depth + 1, offs)
    h1 = _h_from_t(t, sum(m1))
    h2 = _h_from_t(t, sum(m2))
    p1 = decode(h1, m1)
    p2 = decode(h2, m2)
    return all((p2[i] >> 1) == p1[i] for i in range(len(offs)))
