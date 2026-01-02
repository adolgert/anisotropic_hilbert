#!/usr/bin/env python3
"""
Test the "Ceiling Walk" formula from the document to see if it's valid.
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
    if k >= 3 and w != mid_left and w != mid_right:
        return std_entry ^ mid_right  # Toggle bit k-1

    return std_entry

def bits_to_str(x, k):
    return format(x, f'0{k}b')

def test_ceiling_walk(k):
    """Test if ceiling walk creates a valid Hilbert curve."""
    print(f"\n{'='*70}")
    print(f"Testing Ceiling Walk for k={k}")
    print(f"{'='*70}")

    n = 1 << k
    mid_left = (1 << (k-1)) - 1
    mid_right = 1 << (k-1)

    print(f"Midpoint indices: {mid_left}, {mid_right}")

    # Compute h_w sequence
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

    print(f"\nEntry sequence ℓ_w:")
    for w in range(n):
        curr = current_child_entry(w, k)
        toggle = "TOGGLE" if w not in {mid_left, mid_right} and k >= 3 else "---"
        print(f"  w={w}: ℓ={bits_to_str(ell[w], k)} (current={bits_to_str(curr, k)}) {toggle}")

    print(f"\nMismatch state s_w = h_w ⊕ ℓ_w:")
    for w in range(n):
        print(f"  s_{w} = {bits_to_str(s[w], k)}")

    # Check constraints
    print(f"\n{'='*70}")
    print("Checking constraints:")
    print(f"{'='*70}")

    # Constraint 1: s_0 = 0
    if s[0] == 0:
        print(f"✓ s_0 = 0 (correct)")
    else:
        print(f"✗ s_0 = {bits_to_str(s[0], k)} ≠ 0 (VIOLATED!)")
        print(f"  Initial condition fails!")
        return False

    # Constraint 2: Neighbor steps (Hamming distance 1)
    valid = True
    for w in range(n - 1):
        diff = s[w] ^ s[w + 1]
        hamming = bin(diff).count('1')
        if hamming == 1:
            axis = 0
            while ((diff >> axis) & 1) == 0:
                axis += 1
            print(f"✓ s_{w} → s_{w+1}: {bits_to_str(s[w], k)} → {bits_to_str(s[w+1], k)}, flip bit {axis}")
        else:
            print(f"✗ s_{w} → s_{w+1}: {bits_to_str(s[w], k)} → {bits_to_str(s[w+1], k)}, Hamming={hamming} (NOT NEIGHBORS!)")
            valid = False
            # Show first few failures then stop
            if w < 5 or w == n - 2:
                continue
            else:
                print(f"  ... (more violations)")
                break

    if not valid:
        print(f"\n✗ Ceiling Walk formula is INVALID for k={k}")
        print(f"  The formula violates the neighbor constraint.")
        return False

    # Constraint 3: Face constraint (check if needed)
    print(f"\n✓ All neighbor constraints satisfied!")
    return True

if __name__ == "__main__":
    # Test for k=3, 4, 5
    for k in [3, 4, 5]:
        result = test_ceiling_walk(k)
        if not result:
            print(f"\nConclusion: The Ceiling Walk formula is INCORRECT.")
            print(f"It fails basic constraints even for small k.")
            break

    # Show what the formula tries to do
    print(f"\n{'='*70}")
    print("Analysis of the Ceiling Walk Formula")
    print(f"{'='*70}")
    print("""
The formula tries to toggle bit k-1 for ALL positions except the midpoint.

For k=3:
- It toggles bit 2 for w ∈ {0,1,2,5,6,7} (all except w=3,4)
- This creates ℓ_w values that differ from current by XOR with 0b100

Problems:
1. At w=0: ℓ_0 = 0 ⊕ 100 = 100, so s_0 = 0 ⊕ 100 = 100 ≠ 0
   This violates the initial condition s_0 = 0.

2. Even if we exempt w=0, the massive changes break the neighbor constraint.
   You can't toggle a bit at MANY consecutive positions and maintain
   Hamming distance 1 between consecutive s_w values.

The valid alternatives I found only change ONE or TWO positions,
not nearly all positions. For example:
- Path 12: XOR with 0b101 only at w=5
- Path 5: XOR with 0b101 only at w=3
- Path 9: XOR with 0b101 only at w=7

The Ceiling Walk formula is trying to do too much at once.
    """)
