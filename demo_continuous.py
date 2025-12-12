"""demo_continuous.py

Small demo of the *continuous* anisotropic Hilbert curve approximation.

Run:
  python demo_continuous.py
"""

from __future__ import annotations

from continuous_anisotropic_hilbert import eval_point


def main() -> None:
    offsets = (1, 0)  # target box [0,2] x [0,1]
    print(f"Offsets (dyadic box exponents): {offsets}")

    for depth in [1, 2, 3, 6]:
        print(f"\nDepth={depth}")
        for t in [0.0, 0.1, 0.123456, 0.5, 0.9, 0.999]:
            p = eval_point(t, offsets, depth, center=True, normalize_to_unit=False)
            print(f"  t={t:0.6f} -> {p}")

    # Unit-cube normalization example.
    print("\nSame curve normalized to [0,1]^2:")
    for depth in [3, 6]:
        p = eval_point(0.123456, offsets, depth, center=True, normalize_to_unit=True)
        print(f"  depth={depth} -> {p}")


if __name__ == "__main__":
    main()
