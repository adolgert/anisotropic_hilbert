#!/usr/bin/env python3
"""
Detailed test of the "Ceiling Walk" formula for k=5.
"""

def gray_code(w):
    return w ^ (w >> 1)

def rotl_bits(x, r, k):
    if k == 0:
        return x
    r = r % k
    if r == 0:
        return x
    mask = (1 << k) - 1
    return ((x << r) | (x >> (k - r))) & mask

def current_child_entry(w, k):
    """Current implementation."""
    if w == 0:
        return 0
    idx = (w - 1) & ~1
    g = gray_code(idx)
    return rotl_bits(g, 1, k)

def ceiling_walk_entry(w, k):
    """Ceiling Walk formula from the document."""
    std_entry = current_child_entry(w, k)

    # The midpoint indices
    mid_right = 1 << (k - 1)
    mid_left = mid_right - 1

    # Toggle top bit for all w except the midpoint pair
    if k >= 4 and w != mid_left and w != mid_right:
        return std_entry ^ mid_right  # Toggle bit k-1

    return std_entry

def bits_to_str(x, k):
    return format(x, f'0{k}b')

def test_ceiling_walk_k5():
    """Test ceiling walk for k=5."""
    k = 5
    n = 1 << k  # 32 subcubes
    mid_left = (1 << (k-1)) - 1   # 15
    mid_right = 1 << (k-1)         # 16

    print(f"{'='*70}")
    print(f"Testing Ceiling Walk for k={k}")
    print(f"{'='*70}")
    print(f"Number of subcubes: {n}")
    print(f"Midpoint indices: {mid_left}, {mid_right}")
    print(f"Top bit to toggle: bit {k-1} (0b{1 << (k-1):05b})")

    # Compute h_w sequence (rotated BRGC)
    h = []
    for w in range(n):
        g = gray_code(w)
        h_w = rotl_bits(g, 1, k)
        h.append(h_w)

    # Compute ℓ_w using ceiling walk
    ell = []
    for w in range(n):
        ell_w = ceiling_walk_entry(w, k)
        ell.append(ell_w)

    # Compute s_w = h_w ⊕ ℓ_w
    s = []
    for w in range(n):
        s_w = h[w] ^ ell[w]
        s.append(s_w)

    # First, check initial condition
    print(f"\n{'='*70}")
    print("Constraint 1: Initial Condition")
    print(f"{'='*70}")
    print(f"s_0 = {bits_to_str(s[0], k)}")
    print(f"  h_0 = {bits_to_str(h[0], k)}")
    print(f"  ℓ_0 = {bits_to_str(ell[0], k)} (toggled from {bits_to_str(current_child_entry(0, k), k)})")

    if s[0] == 0:
        print(f"✓ s_0 = 0 (PASS)")
        initial_valid = True
    else:
        print(f"✗ s_0 ≠ 0 (FAIL)")
        initial_valid = False

    # Check neighbor constraint
    print(f"\n{'='*70}")
    print("Constraint 2: Neighbor Steps (first 20 transitions)")
    print(f"{'='*70}")

    violations = []
    for w in range(min(20, n - 1)):
        diff = s[w] ^ s[w + 1]
        hamming = bin(diff).count('1')

        if hamming == 1:
            axis = 0
            while ((diff >> axis) & 1) == 0:
                axis += 1
            status = "✓"
        else:
            status = "✗"
            violations.append(w)

        print(f"{status} s_{w:2d} → s_{w+1:2d}: {bits_to_str(s[w], k)} → {bits_to_str(s[w+1], k)}, H={hamming}")

    if w < n - 2:
        print(f"\n... checking remaining transitions ...")
        for w in range(20, n - 1):
            diff = s[w] ^ s[w + 1]
            hamming = bin(diff).count('1')
            if hamming != 1:
                violations.append(w)

    print(f"\n{'='*70}")
    print("Summary")
    print(f"{'='*70}")
    print(f"Initial condition: {'PASS ✓' if initial_valid else 'FAIL ✗'}")
    print(f"Neighbor violations: {len(violations)} out of {n-1} transitions")

    if violations:
        print(f"\nFirst few violations at w = {violations[:10]}")
        if len(violations) > 10:
            print(f"... and {len(violations) - 10} more")
        return False
    else:
        print(f"✓ All neighbor constraints satisfied!")

        # Check face constraint
        print(f"\n{'='*70}")
        print("Constraint 3: Face Constraint")
        print(f"{'='*70}")

        # Compute d_w (Gray code step directions)
        face_violations = 0
        for w in range(n - 1):
            diff_h = h[w] ^ h[w + 1]
            d_w = 0
            while ((diff_h >> d_w) & 1) == 0:
                d_w += 1

            # Check if (s_{w+1})_{d_w} = 1
            bit_value = (s[w + 1] >> d_w) & 1

            if w < 10 or w >= n - 2:  # Show first few and last
                status = "✓" if bit_value == 1 else "✗"
                print(f"{status} w={w:2d}: d_w={d_w}, (s_{w+1:2d})_{d_w} = {bit_value}")

            if bit_value != 1:
                face_violations += 1

        print(f"\nFace constraint violations: {face_violations} out of {n-1} transitions")

        if face_violations == 0:
            print(f"\n{'='*70}")
            print(f"✓✓✓ CEILING WALK IS VALID FOR k={k}! ✓✓✓")
            print(f"{'='*70}")
            return True
        else:
            return False

if __name__ == "__main__":
    result = test_ceiling_walk_k5()

    if result:
        print("\nConclusion: The Ceiling Walk formula WORKS for k=5!")
    else:
        print("\nConclusion: The Ceiling Walk formula FAILS for k=5.")
