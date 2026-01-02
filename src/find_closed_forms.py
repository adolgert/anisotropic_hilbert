#!/usr/bin/env python3
"""
Systematically search for closed-form formulas for alternative paths.
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

def ctz(w):
    """Count trailing zeros."""
    if w == 0:
        return 32
    count = 0
    while (w & 1) == 0:
        count += 1
        w >>= 1
    return count

def trailing_ones(w):
    """Count trailing ones."""
    count = 0
    while (w & 1) != 0:
        count += 1
        w >>= 1
    return count

def popcount(w):
    """Count number of 1 bits."""
    return bin(w).count('1')

def bits_to_str(x, k):
    return format(x, f'0{k}b')

# Try different index selection functions
def try_formula(entry_seq, k, formula_name, index_func, xor_mask_func=None):
    """
    Try: ℓ_w = rotL(G(index_func(w)), 1, k) [⊕ xor_mask_func(w)]
    """
    n = len(entry_seq)
    matches = True
    details = []

    for w in range(n):
        if w == 0:
            predicted = 0
        else:
            idx = index_func(w)
            predicted = rotl_bits(gray_code(idx), 1, k)
            if xor_mask_func:
                predicted ^= xor_mask_func(w, k)

        match = (predicted == entry_seq[w])
        if not match:
            matches = False

        details.append({
            'w': w,
            'predicted': predicted,
            'actual': entry_seq[w],
            'match': match
        })

    return matches, details

def test_all_formulas(name, entry_seq, k):
    """Test various formulas against an entry sequence."""
    print(f"\n{'='*70}")
    print(f"Finding closed form for: {name}")
    print(f"{'='*70}")
    print(f"Target entry sequence: {[bits_to_str(e, k) for e in entry_seq]}")

    # Define various index functions to try
    index_functions = {
        "(w-1) & ~1 [current]": lambda w: (w-1) & ~1 if w > 0 else 0,
        "(w-1) | 1": lambda w: (w-1) | 1 if w > 0 else 0,
        "w & ~1": lambda w: w & ~1,
        "w | 1": lambda w: w | 1,
        "w ^ 1": lambda w: w ^ 1,
        "w": lambda w: w,
        "((w-1) & ~1) ^ (w & 4)": lambda w: ((w-1) & ~1) ^ (w & 4) if w > 0 else 0,
        "conditional: w=5?0:((w-1)&~1)": lambda w: 0 if w == 5 else ((w-1) & ~1 if w > 0 else 0),
        "conditional: w=3?(w-1)|1:((w-1)&~1)": lambda w: ((w-1) | 1) if w == 3 else ((w-1) & ~1 if w > 0 else 0),
        "conditional: w=7?(w-3)&~1:((w-1)&~1)": lambda w: ((w-3) & ~1) if w == 7 else ((w-1) & ~1 if w > 0 else 0),
    }

    # XOR mask functions
    xor_masks = {
        "none": None,
        "bit 0 if w=5": lambda w, k: (1 << 0) if w == 5 else 0,
        "bit 2 if w=5": lambda w, k: (1 << 2) if w == 5 else 0,
        "0b101 if w=5": lambda w, k: 0b101 if w == 5 else 0,
        "0b101 if w=3": lambda w, k: 0b101 if w == 3 else 0,
        "0b101 if w=7": lambda w, k: 0b101 if w == 7 else 0,
        "0b101 if w in {3,5,7}": lambda w, k: 0b101 if w in {3, 5, 7} else 0,
    }

    found_formulas = []

    for idx_name, idx_func in index_functions.items():
        for mask_name, mask_func in xor_masks.items():
            if mask_name == "none" and mask_func is None:
                formula_desc = f"rotL(G({idx_name}), 1, k)"
            else:
                formula_desc = f"rotL(G({idx_name}), 1, k) ⊕ {mask_name}"

            matches, _ = try_formula(entry_seq, k, formula_desc, idx_func, mask_func)
            if matches:
                found_formulas.append(formula_desc)

    if found_formulas:
        print(f"\n✓ Found {len(found_formulas)} working formula(s):")
        for formula in found_formulas:
            print(f"  • ℓ_w = {formula}")
    else:
        print(f"\n✗ No simple formula found")

    # Now try to derive child_dir formula
    print(f"\nAnalyzing child_dir pattern...")
    print(f"  (child_dir is the axis that changes in s_w)")

    # Compute s_w from entry_seq
    # We need h_w for this
    h_seq = []
    for w in range(len(entry_seq)):
        g = gray_code(w)
        h_w = rotl_bits(g, 1, k)
        h_seq.append(h_w)

    s_seq = [h_seq[w] ^ entry_seq[w] for w in range(len(entry_seq))]
    print(f"  s_w sequence: {[bits_to_str(s, k) for s in s_seq]}")

    # Compute directions
    directions = []
    for w in range(len(s_seq) - 1):
        diff = s_seq[w] ^ s_seq[w + 1]
        axis = 0
        while axis < k and ((diff >> axis) & 1) == 0:
            axis += 1
        directions.append(axis)

    print(f"  a_w values:   {directions}")

    # Try to find pattern in directions
    current_dirs = []
    for w in range(len(directions)):
        if w == 0:
            current_dirs.append(1)
        elif w & 1:  # odd
            current_dirs.append((trailing_ones(w) + 1) % k)
        else:  # even
            current_dirs.append((trailing_ones(w - 1) + 1) % k)

    print(f"  current a_w:  {current_dirs}")
    print(f"  matches:      {['✓' if directions[i] == current_dirs[i] else '✗' for i in range(len(directions))]}")

    # Look for patterns
    diffs = [i for i in range(len(directions)) if directions[i] != current_dirs[i]]
    if diffs:
        print(f"\n  Differences at w = {diffs}")
        for w in diffs:
            print(f"    w={w}: alternative={directions[w]}, current={current_dirs[w]}")

            # Try simple modifications
            print(f"      w={w} ({bits_to_str(w, k)}): popcount={popcount(w)}, w%4={w%4}, ctz={ctz(w) if w > 0 else '-'}")

if __name__ == "__main__":
    k = 3

    # Test the interesting alternatives
    alternatives = {
        "Path 5 (diff @ w=3 only)": [0b000, 0b000, 0b000, 0b011, 0b110, 0b101, 0b101, 0b011],
        "Path 9 (diff @ w=7 only)": [0b000, 0b000, 0b000, 0b110, 0b110, 0b101, 0b101, 0b110],
        "Path 12 (diff @ w=5 only)": [0b000, 0b000, 0b000, 0b110, 0b110, 0b000, 0b101, 0b011],
        "Path 1 (high bit 2)": [0b000, 0b000, 0b000, 0b011, 0b000, 0b000, 0b101, 0b110],
    }

    for name, entry_seq in alternatives.items():
        test_all_formulas(name, entry_seq, k)
