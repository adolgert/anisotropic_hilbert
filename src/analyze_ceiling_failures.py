#!/usr/bin/env python3
"""
Detailed analysis of where and why the Ceiling Walk formula fails.
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
    if w == 0:
        return 0
    idx = (w - 1) & ~1
    g = gray_code(idx)
    return rotl_bits(g, 1, k)

def ceiling_walk_entry(w, k):
    std_entry = current_child_entry(w, k)
    mid_right = 1 << (k - 1)
    mid_left = mid_right - 1

    if k >= 4 and w != mid_left and w != mid_right:
        return std_entry ^ mid_right
    return std_entry

def bits_to_str(x, k):
    return format(x, f'0{k}b')

def analyze_failures(k):
    """Analyze the specific failure points."""
    n = 1 << k
    mid_left = (1 << (k-1)) - 1
    mid_right = 1 << (k-1)

    print(f"{'='*70}")
    print(f"Analyzing Ceiling Walk Failures for k={k}")
    print(f"{'='*70}")
    print(f"mid_left = {mid_left}, mid_right = {mid_right}")

    # Compute sequences
    h = [rotl_bits(gray_code(w), 1, k) for w in range(n)]
    ell = [ceiling_walk_entry(w, k) for w in range(n)]
    s = [h[w] ^ ell[w] for w in range(n)]

    # Analyze around the midpoint
    print(f"\n{'='*70}")
    print("Detail around midpoint:")
    print(f"{'='*70}")

    for w in range(max(0, mid_left - 2), min(n, mid_right + 3)):
        toggled = "NO" if w in {mid_left, mid_right} else "YES"
        std_entry = current_child_entry(w, k)

        print(f"\nw={w:2d} (toggled={toggled}):")
        print(f"  h_w  = {bits_to_str(h[w], k)}")
        print(f"  ℓ_w  = {bits_to_str(ell[w], k)} (std: {bits_to_str(std_entry, k)})")
        print(f"  s_w  = {bits_to_str(s[w], k)}")

        if w < n - 1:
            diff = s[w] ^ s[w + 1]
            hamming = bin(diff).count('1')
            status = "✓" if hamming == 1 else f"✗ H={hamming}"
            print(f"  s_{w} → s_{w+1}: {status}")

    # Explain the problem
    print(f"\n{'='*70}")
    print("Problem Analysis:")
    print(f"{'='*70}")

    print(f"\nThe failures occur at transitions involving the midpoint boundary.")
    print(f"\nAt w=14 (just before mid_left=15):")
    print(f"  - w=14 is toggled: s_14 has bit 4 set")
    print(f"  - w=15 is NOT toggled: s_15 does NOT have bit 4 set")
    print(f"  - Transition 14→15 must flip BOTH another bit AND bit 4")
    print(f"  - This requires Hamming distance 2, violating the neighbor constraint!")

    print(f"\nAt w=16 (mid_right):")
    print(f"  - w=16 is NOT toggled: s_16 does NOT have bit 4 set")
    print(f"  - w=17 is toggled: s_17 has bit 4 set")
    print(f"  - Transition 16→17 must flip BOTH another bit AND bit 4")
    print(f"  - This again requires Hamming distance 2!")

    print(f"\n{'='*70}")
    print("Why the formula is fundamentally flawed:")
    print(f"{'='*70}")
    print("""
The Ceiling Walk tries to toggle bit k-1 everywhere EXCEPT at the midpoint pair.
This creates a "discontinuity" where:
  - Before mid_left: bit k-1 is SET (ceiling)
  - At mid_left, mid_right: bit k-1 follows standard (floor)
  - After mid_right: bit k-1 is SET (ceiling)

The problem is that you can't jump from ceiling→floor or floor→ceiling
while ALSO taking the required step for the walk constraint.
You need TWO bit flips:
  1. One to satisfy the walk constraint (flip some axis a_w)
  2. One to change the ceiling/floor state (flip bit k-1)

But s_w must be a Hamiltonian path (neighbors only), so you can only flip ONE bit.

The document even acknowledges this issue in the text:
  "Wait, is the jump from 'floor' to 'ceiling' valid here?"
  "Correction: The mask logic requires that we only stay on the floor
   for the blocks adjacent to the high-axis crossing."

But the proposed fix doesn't work either!
    """)

if __name__ == "__main__":
    for k in [3, 4, 5]:
        analyze_failures(k)
        print("\n")
