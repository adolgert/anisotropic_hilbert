"""
anisotropic_hilbert_c.py

Python ctypes wrapper for the C implementation of anisotropic Hilbert curves.

This module provides the same API as anisotropic_hilbert.py but uses the
optimized C library for performance.

Usage:
    from anisotropic_hilbert_c import encode, decode, iter_points

    # Same API as the pure Python version
    h = encode((3, 5), (4, 4))
    point = decode(42, (4, 4))
"""

from __future__ import annotations

import ctypes
import os
import sys
from pathlib import Path
from typing import Iterable, Sequence, Tuple

# Find and load the shared library
def _load_library():
    """Load the C shared library."""
    # Determine library name based on platform
    if sys.platform == 'darwin':
        libname = 'libanisotropic_hilbert.dylib'
    else:
        libname = 'libanisotropic_hilbert.so'

    # Search paths: same directory as this file, then current directory
    search_paths = [
        Path(__file__).parent / libname,
        Path.cwd() / libname,
    ]

    for path in search_paths:
        if path.exists():
            return ctypes.CDLL(str(path))

    raise OSError(
        f"Could not find {libname}. "
        f"Run 'make' to build the C library first. "
        f"Searched: {[str(p) for p in search_paths]}"
    )

_lib = _load_library()

# Type definitions
_coord_t = ctypes.c_uint32
_coord_array = ctypes.POINTER(_coord_t)
_int_array = ctypes.POINTER(ctypes.c_int)

# Function signatures
_lib.hilbert_encode_64.argtypes = [_coord_array, _int_array, ctypes.c_int]
_lib.hilbert_encode_64.restype = ctypes.c_uint64

_lib.hilbert_decode_64.argtypes = [ctypes.c_uint64, _int_array, ctypes.c_int, _coord_array]
_lib.hilbert_decode_64.restype = None

_lib.hilbert_encode_128.argtypes = [
    _coord_array, _int_array, ctypes.c_int,
    ctypes.POINTER(ctypes.c_uint64), ctypes.POINTER(ctypes.c_uint64)
]
_lib.hilbert_encode_128.restype = None

_lib.hilbert_decode_128.argtypes = [
    ctypes.c_uint64, ctypes.c_uint64, _int_array, ctypes.c_int, _coord_array
]
_lib.hilbert_decode_128.restype = None

_lib.hilbert_decode_batch_64.argtypes = [
    ctypes.c_uint64, ctypes.c_uint64, _int_array, ctypes.c_int, _coord_array
]
_lib.hilbert_decode_batch_64.restype = None

_lib.hilbert_index_bits.argtypes = [_int_array, ctypes.c_int]
_lib.hilbert_index_bits.restype = ctypes.c_int


def _make_m_array(m: Sequence[int]) -> Tuple[ctypes.Array, int]:
    """Convert Python sequence to C int array."""
    n = len(m)
    m_arr = (ctypes.c_int * n)(*m)
    return m_arr, n


def _make_coord_array(point: Sequence[int]) -> ctypes.Array:
    """Convert Python sequence to C coord array."""
    return (_coord_t * len(point))(*point)


def index_bit_length(m: Sequence[int]) -> int:
    """Total number of bits in the Hilbert index."""
    m_arr, n = _make_m_array(m)
    return _lib.hilbert_index_bits(m_arr, n)


def encode(point: Sequence[int], m: Sequence[int]) -> int:
    """
    Map an n-D integer lattice point to its anisotropic Hilbert index.

    Parameters
    ----------
    point : sequence of ints
        Coordinates (p0,...,p_{n-1}) with 0 <= pj < 2^{m_j}.
    m : sequence of ints
        Exponents (m0,...,m_{n-1}) describing the box size.

    Returns
    -------
    h : int
        Hilbert index in [0, 2^{sum(m)}).
    """
    m_arr, n = _make_m_array(m)
    point_arr = _make_coord_array(point)
    total_bits = sum(m)

    if total_bits <= 64:
        return _lib.hilbert_encode_64(point_arr, m_arr, n)
    else:
        h_lo = ctypes.c_uint64()
        h_hi = ctypes.c_uint64()
        _lib.hilbert_encode_128(point_arr, m_arr, n,
                                ctypes.byref(h_lo), ctypes.byref(h_hi))
        return (h_hi.value << 64) | h_lo.value


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
    m_arr, n = _make_m_array(m)
    point_arr = (_coord_t * n)()
    total_bits = sum(m)

    if total_bits <= 64:
        _lib.hilbert_decode_64(h, m_arr, n, point_arr)
    else:
        h_lo = h & ((1 << 64) - 1)
        h_hi = h >> 64
        _lib.hilbert_decode_128(h_lo, h_hi, m_arr, n, point_arr)

    return tuple(point_arr)


def iter_points(m: Sequence[int]) -> Iterable[Tuple[int, ...]]:
    """Iterate all points in curve order (decode 0..2^{sum(m)}-1)."""
    m_tuple = tuple(int(mi) for mi in m)
    M = sum(m_tuple)
    N = 1 << M

    # For small cases, just iterate
    if N <= 1024:
        for h in range(N):
            yield decode(h, m_tuple)
        return

    # For larger cases, use batch decoding for efficiency
    m_arr, n = _make_m_array(m_tuple)
    batch_size = min(4096, N)
    points_arr = (_coord_t * (batch_size * n))()

    for batch_start in range(0, N, batch_size):
        batch_count = min(batch_size, N - batch_start)
        _lib.hilbert_decode_batch_64(batch_start, batch_count, m_arr, n, points_arr)

        for i in range(batch_count):
            yield tuple(points_arr[i * n + j] for j in range(n))


def decode_batch(h_start: int, count: int, m: Sequence[int]) -> list:
    """
    Decode a batch of consecutive Hilbert indices.

    Parameters
    ----------
    h_start : int
        Starting Hilbert index.
    count : int
        Number of consecutive indices to decode.
    m : sequence of ints
        Exponents defining the box.

    Returns
    -------
    points : list of tuples
        List of decoded coordinate tuples.
    """
    m_arr, n = _make_m_array(m)
    points_arr = (_coord_t * (count * n))()

    _lib.hilbert_decode_batch_64(h_start, count, m_arr, n, points_arr)

    return [tuple(points_arr[i * n + j] for j in range(n)) for i in range(count)]
