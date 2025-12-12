"""
demo.py

Small demonstration of the anisotropic Hilbert curve on a few unequal-dimension boxes.
"""

from anisotropic_hilbert import iter_points, encode, decode

def show(m, limit=None):
    print(f"m={m} (box sizes {[1<<mi for mi in m]})")
    pts = list(iter_points(m))
    if limit is not None:
        pts = pts[:limit]
    for h, p in enumerate(pts):
        print(f"{h:4d}: {p}")
    print()

if __name__ == "__main__":
    show((2,1))      # 4x2
    show((3,1))      # 8x2
    show((2,2,1))    # 4x4x2
