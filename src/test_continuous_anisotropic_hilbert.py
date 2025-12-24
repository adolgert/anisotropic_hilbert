"""test_continuous_anisotropic_hilbert.py

Verification tests for the continuous extension wrapper.

These tests do NOT attempt to "prove continuity" in the analytic sense.
Instead, they check the structural properties that are used in the
continuity proof:

  1) Refinement consistency:
       When offsets are fixed and depth increases by 1,
       the decoded integer coordinates refine by one extra LSB per axis:
          p_{k+1} >> 1 == p_k

     This is the concrete statement that coordinate bits are stable under
     deeper refinements (a nested-cell property).

  2) Scaled lattice continuity at fixed depth:
       The scaled polyline at depth k moves by L1 step exactly 2^{-k}.

  3) Approx-inverse correctness at fixed depth:
       If x is the depth-k curve point for parameter interval [h/2^M,(h+1)/2^M),
       then approx_inverse(x) returns that same h.

Run:
  python -m unittest -v
"""

from __future__ import annotations

import os
import sys
import math
import random
import unittest

# Allow running tests from any working directory.
_THIS_DIR = os.path.dirname(os.path.abspath(__file__))
if _THIS_DIR not in sys.path:
    sys.path.insert(0, _THIS_DIR)

from anisotropic_hilbert import decode
from continuous_anisotropic_hilbert import (
    approx_inverse,
    eval_point,
    m_from_offsets,
    refinement_consistency_holds,
)


def manhattan(a, b) -> float:
    return sum(abs(x - y) for x, y in zip(a, b))


class TestContinuousAnisotropicHilbert(unittest.TestCase):
    def test_refinement_consistency_random(self):
        rng = random.Random(0)
        cases = [
            (1, 0),
            (2, 0),
            (3, 1, 0),
            (2, 1, 1, 0),
        ]
        for offsets in cases:
            for depth in range(1, 9):
                for _ in range(50):
                    t = rng.random()
                    ok = refinement_consistency_holds(offsets, depth, t)
                    self.assertTrue(
                        ok,
                        msg=f"refinement failed for offsets={offsets}, depth={depth}, t={t}",
                    )

    def test_scaled_lattice_continuity(self):
        # Keep sizes small enough for exhaustive traversal.
        # Example: offsets (1,0) and depth 3 => m=(4,3) => 2^(7)=128 points.
        offsets = (1, 0)
        depth = 3
        m = m_from_offsets(depth, offsets)
        M = sum(m)
        N = 1 << M

        pts = []
        for h in range(N):
            # Use eval_point at the left endpoint of the h-th interval.
            t = h / float(N)
            pts.append(eval_point(t, offsets, depth, center=False, normalize_to_unit=False))

        step = 1.0 / float(1 << depth)
        for i in range(N - 1):
            dist = manhattan(pts[i], pts[i + 1])
            self.assertAlmostEqual(
                dist,
                step,
                places=12,
                msg=f"scaled step mismatch at {i}->{i+1}: {dist} vs {step}",
            )

    def test_approx_inverse_matches_index(self):
        offsets = (2, 1, 0)
        depth = 4
        m = m_from_offsets(depth, offsets)
        M = sum(m)
        N = 1 << M

        # Sample a set of indices (including edges).
        for h in [0, 1, 2, 3, 7, 31, 127, N - 2, N - 1]:
            if not (0 <= h < N):
                continue
            t = (h + 0.25) / float(N)
            x = eval_point(t, offsets, depth, center=False)
            inv = approx_inverse(x, offsets, depth)
            self.assertEqual(inv.h, h)

    def test_decode_refines_by_bit_shift(self):
        # This is the same as refinement consistency but done deterministically
        # on a few rational t values to catch boundary behavior.
        offsets = (1, 0)
        for depth in range(1, 8):
            for num in [1, 3, 7, 11, 19, 23, 37]:
                t = num / 101.0
                m1 = m_from_offsets(depth, offsets)
                m2 = m_from_offsets(depth + 1, offsets)
                h1 = int(math.floor(t * (1 << sum(m1))))
                h2 = int(math.floor(t * (1 << sum(m2))))
                p1 = decode(h1, m1)
                p2 = decode(h2, m2)
                self.assertTrue(all((p2[i] >> 1) == p1[i] for i in range(len(offsets))))


if __name__ == "__main__":
    unittest.main(verbosity=2)
