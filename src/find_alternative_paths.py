#!/usr/bin/env python3
"""
Search for alternative valid Hilbert curve paths through BRGC in 3D.

We have constraints:
1. s_{w+1} must be a neighbor of s_w (differ by exactly 1 bit)
2. (s_{w+1})_{d_w} = 1 (the bit at position d_w must be set)

where d_w is the axis of the Gray-code step.
"""

def gray_code(w):
    """Standard binary-reflected Gray code."""
    return w ^ (w >> 1)

def rotl_bits(x, r, k):
    """Rotate left by r bits in k-bit space."""
    if k == 0:
        return x
    r = r % k
    if r == 0:
        return x
    mask = (1 << k) - 1
    return ((x << r) | (x >> (k - r))) & mask

def hamming_distance(a, b):
    """Count number of differing bits."""
    return bin(a ^ b).count('1')

def ctz(w):
    """Count trailing zeros."""
    if w == 0:
        return 0
    count = 0
    while (w & 1) == 0:
        count += 1
        w >>= 1
    return count

def compute_brgc_sequence(k):
    """Compute the rotated BRGC sequence and step directions for k dimensions."""
    n = 1 << k  # 2^k subcubes
    h = []
    d = []

    for w in range(n):
        g = gray_code(w)
        h_w = rotl_bits(g, 1, k)
        h.append(h_w)

    # Compute directions (which axis changes)
    for w in range(n - 1):
        diff = h[w] ^ h[w + 1]
        # Find which bit is set
        axis = 0
        while axis < k and ((diff >> axis) & 1) == 0:
            axis += 1
        d.append(axis)

    return h, d

def find_all_valid_paths(k):
    """Find all valid s_w sequences that satisfy the constraints."""
    h, d = compute_brgc_sequence(k)
    n = len(h)

    # DFS to find all valid paths
    valid_paths = []

    def dfs(w, s_seq):
        if w == n:
            valid_paths.append(s_seq[:])
            return

        if w == 0:
            # Start at origin
            s_seq.append(0)
            dfs(1, s_seq)
            s_seq.pop()
        else:
            # s_w must be a neighbor of s_{w-1} (Hamming distance 1)
            # and must have bit d_{w-1} set
            s_prev = s_seq[-1]
            required_bit = d[w - 1]

            # Try all neighbors of s_prev
            for flip_bit in range(k):
                s_candidate = s_prev ^ (1 << flip_bit)

                # Check if required bit is set
                if (s_candidate >> required_bit) & 1:
                    s_seq.append(s_candidate)
                    dfs(w + 1, s_seq)
                    s_seq.pop()

    dfs(0, [])
    return valid_paths

def current_implementation_sw(w, k):
    """Current implementation of s_w."""
    if w == 0:
        return 0
    if w & 1:  # odd
        return 1 << 1  # e_1
    else:  # even
        return (1 << 1) ^ (1 << ((ctz(w) + 1) % k))

def current_implementation_entry(w, k):
    """Current implementation of child_entry."""
    if w == 0:
        return 0
    idx = (w - 1) & ~1
    g = gray_code(idx)
    return rotl_bits(g, 1, k)

def bits_to_str(x, k):
    """Convert integer to k-bit binary string."""
    return format(x, f'0{k}b')

def analyze_path(path, k):
    """Analyze a path and compute child_entry and child_dir."""
    h, d = compute_brgc_sequence(k)
    n = len(path)

    entry = []
    direction = []

    for w in range(n):
        # ℓ^{in}_w = h_w ⊕ s_w
        ell_w = h[w] ^ path[w]
        entry.append(ell_w)

        if w < n - 1:
            # a_w = axis that changes from s_w to s_{w+1}
            diff = path[w] ^ path[w + 1]
            axis = 0
            while axis < k and ((diff >> axis) & 1) == 0:
                axis += 1
            direction.append(axis)

    return entry, direction

if __name__ == "__main__":
    k = 3
    print(f"Finding all valid paths for k={k} dimensions")
    print("=" * 60)

    h, d = compute_brgc_sequence(k)
    print(f"\nRotated BRGC sequence h_w:")
    for w, h_w in enumerate(h):
        print(f"  h_{w} = {bits_to_str(h_w, k)}")

    print(f"\nStep directions d_w:")
    for w, d_w in enumerate(d):
        print(f"  d_{w} = {d_w}")

    print("\nSearching for valid s_w sequences...")
    valid_paths = find_all_valid_paths(k)

    print(f"\nFound {len(valid_paths)} valid path(s)!\n")

    # Analyze each path
    for path_idx, path in enumerate(valid_paths):
        print(f"Path {path_idx + 1}:")
        print(f"  s_w sequence: {[bits_to_str(s, k) for s in path]}")

        entry, direction = analyze_path(path, k)

        print(f"  ℓ^{{in}}_w:    {[bits_to_str(ell, k) for ell in entry]}")
        print(f"  a_w (dir):    {direction}")

        # Compare with current implementation
        current_s = [current_implementation_sw(w, k) for w in range(len(path))]
        current_entry = [current_implementation_entry(w, k) for w in range(len(path))]

        if path == current_s:
            print(f"  >>> This is the CURRENT implementation")
        else:
            print(f"  >>> This is an ALTERNATIVE solution!")
            print(f"  Current s_w:  {[bits_to_str(s, k) for s in current_s]}")
            print(f"  Differences at w = {[w for w in range(len(path)) if path[w] != current_s[w]]}")

        print()
