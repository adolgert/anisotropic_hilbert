"""
test_anisotropic_hilbert.py

Unit tests for anisotropic_hilbert.py.

The core properties tested:
  1) Lattice continuity:
       Manhattan distance between consecutive curve points is exactly 1.
  2) Bijection / round-trip:
       encode(decode(h)) == h for all h
       decode(encode(p)) == p for all points p in the box
  3) Bounds / uniqueness:
       all points are within bounds and unique

Environment variables:
  SLOW_TESTS=1    Enable 5D exhaustive tests (~1000 shapes, max 32K points)
  GLACIAL_TESTS=1 Enable 100 random large tests across 2D-7D (up to ~268M points)
  GLACIAL_SEED=N  Set random seed for reproducible GLACIAL_TESTS runs

The tests automatically use the C implementation if available (run `make` first),
falling back to pure Python otherwise.
"""

from __future__ import annotations

import os
import itertools
import random
import unittest

# Try to use C implementation, fall back to Python
try:
    from anisotropic_hilbert_c import encode, decode
    _USING_C = True
except OSError:
    from anisotropic_hilbert import encode, decode
    _USING_C = False


def manhattan(a, b) -> int:
    return sum(abs(x - y) for x, y in zip(a, b))


def shape_size(m):
    return 1 << sum(m)


class TestAnisotropicHilbert(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        impl = "C" if _USING_C else "Python"
        print(f"\nUsing {impl} implementation")

    def check_shape(self, m):
        m = tuple(m)
        n = len(m)
        N = shape_size(m)

        pts = [decode(h, m) for h in range(N)]

        # uniqueness
        self.assertEqual(len(set(pts)), N, f"duplicates for shape m={m}")

        # bounds
        for p in pts:
            self.assertEqual(len(p), n)
            for j, mj in enumerate(m):
                bound = (1 << mj) if mj > 0 else 1
                self.assertTrue(0 <= p[j] < bound, f"out of bounds p={p} for m={m}")

        # lattice continuity: Manhattan step == 1
        for i in range(N - 1):
            dist = manhattan(pts[i], pts[i + 1])
            self.assertEqual(dist, 1, f"non-adjacent at {i}->{i+1}: {pts[i]}->{pts[i+1]} (dist {dist}), m={m}")

        # round-trip: encode(decode(h)) == h
        for h, p in enumerate(pts):
            self.assertEqual(encode(p, m), h, f"encode mismatch: h={h}, p={p}, m={m}")
            self.assertEqual(decode(h, m), p, f"decode mismatch: h={h}, m={m}")

    def test_named_shapes(self):
        # 4x2, 8x2, 4x4x2
        for m in [
            (2, 1),
            (3, 1),
            (2, 2, 1),
            (3, 2, 1),
            (3, 3, 1),
            (1, 4),
            (4, 1),
            (0, 2, 1),
        ]:
            with self.subTest(m=m):
                self.check_shape(m)

    def test_exhaustive_2d_up_to_32(self):
        # n=2, exponents 0..5 => max side length 32, max points 1024
        for m in itertools.product(range(0, 6), repeat=2):
            if all(x == 0 for x in m):
                continue
            with self.subTest(m=m):
                self.check_shape(m)

    def test_exhaustive_3d_up_to_16(self):
        # n=3, exponents 0..4 => max points 4096
        for m in itertools.product(range(0, 5), repeat=3):
            if all(x == 0 for x in m):
                continue
            with self.subTest(m=m):
                self.check_shape(m)

    def test_exhaustive_4d_up_to_8(self):
        # n=4, exponents 0..3 => max points 4096
        for m in itertools.product(range(0, 4), repeat=4):
            if all(x == 0 for x in m):
                continue
            with self.subTest(m=m):
                self.check_shape(m)

    def test_exhaustive_5d_optional_slow(self):
        # Optional: n=5, exponents 0..3 => 1023 shapes, max points 32768
        # Enable with: SLOW_TESTS=1 python -m unittest -v
        if os.environ.get("SLOW_TESTS") != "1":
            self.skipTest("Set SLOW_TESTS=1 to enable the 5D exhaustive test.")
        for m in itertools.product(range(0, 4), repeat=5):
            if all(x == 0 for x in m):
                continue
            with self.subTest(m=m):
                self.check_shape(m)

    def test_glacial_random_large_shapes(self):
        """
        100 random large test cases across 2D-7D, staying under 50% of 62GB RAM.

        Memory constraint: sum(m) <= 28 ensures each test uses < 31 GB.
        The test space spans shapes with exponents up to:
          2D: 0-14, 3D: 0-9, 4D: 0-7, 5D: 0-5, 6D: 0-4, 7D: 0-4

        Sampling is stratified: ~16-17 tests per dimension to ensure coverage.

        Enable with: GLACIAL_TESTS=1 python -m unittest -v
        Optionally set GLACIAL_SEED=<int> for reproducible runs.
        """
        if os.environ.get("GLACIAL_TESTS") != "1":
            self.skipTest("Set GLACIAL_TESTS=1 to enable random large shape tests.")

        # Max exponent per dimension to stay under ~50% RAM (sum(m) <= 28)
        max_exp_by_dims = {
            2: 14,  # max sum = 28, 224 shapes
            3: 9,   # max sum = 27, 999 shapes
            4: 7,   # max sum = 28, 4095 shapes
            5: 5,   # max sum = 25, 7775 shapes
            6: 4,   # max sum = 24, 15624 shapes
            7: 4,   # max sum = 28, 78124 shapes
        }

        # Build candidate pools per dimension
        candidates_by_dim = {}
        for dims in range(2, 8):
            max_exp = max_exp_by_dims[dims]
            candidates_by_dim[dims] = [
                m for m in itertools.product(range(0, max_exp + 1), repeat=dims)
                if not all(x == 0 for x in m) and sum(m) <= 28
            ]

        # Seed for reproducibility (optional)
        seed_str = os.environ.get("GLACIAL_SEED")
        seed = int(seed_str) if seed_str else None
        rng = random.Random(seed)

        # Stratified sampling: ~16-17 tests per dimension (100 total across 6 dims)
        n_total = 100
        n_dims = 6
        base_per_dim = n_total // n_dims  # 16
        extra = n_total % n_dims  # 4

        selected = []
        for i, dims in enumerate(range(2, 8)):
            n_for_dim = base_per_dim + (1 if i < extra else 0)
            pool = candidates_by_dim[dims]
            n_for_dim = min(n_for_dim, len(pool))
            selected.extend(rng.sample(pool, n_for_dim))

        rng.shuffle(selected)

        for m in selected:
            with self.subTest(m=m, points=1 << sum(m)):
                self.check_shape(m)


if __name__ == "__main__":
    unittest.main(verbosity=2)
