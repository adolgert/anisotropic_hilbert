#!/usr/bin/env python3
"""
Analyze the patterns in alternative child_entry and child_dir formulas.
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
        return 32  # or some large number
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

def bits_to_str(x, k):
    return format(x, f'0{k}b')

def current_child_entry(w, k):
    """Current implementation."""
    if w == 0:
        return 0
    idx = (w - 1) & ~1
    g = gray_code(idx)
    return rotl_bits(g, 1, k)

def current_child_dir(w, k):
    """Current implementation."""
    if w == 0:
        return 1
    if w & 1:  # odd
        return (trailing_ones(w) + 1) % k
    else:  # even
        return (trailing_ones(w - 1) + 1) % k

# Alternative solutions from our search
alternatives = {
    "Path 5 (minimal diff @ w=3)": {
        "entry": [0b000, 0b000, 0b000, 0b011, 0b110, 0b101, 0b101, 0b011],
        "dir":   [1, 2, 0, 2, 0, 2, 2]
    },
    "Path 9 (minimal diff @ w=7)": {
        "entry": [0b000, 0b000, 0b000, 0b110, 0b110, 0b101, 0b101, 0b110],
        "dir":   [1, 2, 2, 0, 0, 2, 0]
    },
    "Path 12 (minimal diff @ w=5)": {
        "entry": [0b000, 0b000, 0b000, 0b110, 0b110, 0b000, 0b101, 0b011],
        "dir":   [1, 2, 2, 0, 2, 0, 2]
    },
    "Path 1 (many diffs)": {
        "entry": [0b000, 0b000, 0b000, 0b011, 0b000, 0b000, 0b101, 0b110],
        "dir":   [1, 2, 0, 1, 1, 0, 0]
    }
}

def analyze_alternative(name, alt_data, k):
    """Analyze an alternative to find patterns."""
    print(f"\n{'=' * 70}")
    print(f"Analyzing: {name}")
    print(f"{'=' * 70}")

    entry = alt_data["entry"]
    direction = alt_data["dir"]

    print("\nEntry sequence ℓ^{in}_w:")
    for w in range(len(entry)):
        curr_entry = current_child_entry(w, k)
        match = "✓" if entry[w] == curr_entry else "✗"
        print(f"  w={w}: {bits_to_str(entry[w], k)} {match} (current: {bits_to_str(curr_entry, k)})")

    print("\nDirection sequence a_w:")
    for w in range(len(direction)):
        curr_dir = current_child_dir(w, k)
        match = "✓" if direction[w] == curr_dir else "✗"
        print(f"  w={w}: a_{w} = {direction[w]} {match} (current: {curr_dir})")

    # Try to find patterns
    print("\nLooking for patterns in entry sequence...")

    # Check if it's related to current formula with XOR correction
    print("\nXOR difference from current:")
    for w in range(len(entry)):
        curr = current_child_entry(w, k)
        diff = entry[w] ^ curr
        if diff != 0:
            print(f"  w={w}: ℓ_alt ⊕ ℓ_cur = {bits_to_str(diff, k)}")

    # Check for patterns based on w's properties
    print("\nChecking w-based patterns:")
    for w in range(len(entry)):
        print(f"  w={w} ({bits_to_str(w, k)}): entry={bits_to_str(entry[w], k)}, "
              f"w%2={w%2}, w%4={w%4}, ctz={ctz(w) if w > 0 else '-'}")

    # Try simple formulas
    print("\nTrying formula: ℓ_w = rotL(G(f(w)), 1, k)")
    for func_name, func in [
        ("(w-1) & ~1", lambda w: (w-1) & ~1 if w > 0 else 0),
        ("w & ~1", lambda w: w & ~1),
        ("w | 1 if w>=3", lambda w: w | 1 if w >= 3 else ((w-1) & ~1 if w > 0 else 0)),
    ]:
        print(f"\n  Testing f(w) = {func_name}:")
        matches = True
        for w in range(len(entry)):
            idx = func(w)
            predicted = rotl_bits(gray_code(idx), 1, k) if w > 0 else 0
            if predicted == entry[w]:
                print(f"    w={w}: ✓ (idx={idx})")
            else:
                print(f"    w={w}: ✗ predicted={bits_to_str(predicted, k)}, actual={bits_to_str(entry[w], k)}")
                matches = False
        if matches:
            print(f"  >>> FORMULA WORKS: ℓ_w = rotL(G({func_name}), 1, k)")

if __name__ == "__main__":
    k = 3

    print("Current implementation:")
    print("=" * 70)
    for w in range(8):
        entry = current_child_entry(w, k)
        direction = current_child_dir(w, k) if w < 7 else None
        print(f"w={w}: ℓ_{w} = {bits_to_str(entry, k)}, a_{w} = {direction}")

    for name, data in alternatives.items():
        analyze_alternative(name, data, k)

    # Let's specifically analyze Path 12 which seems promising
    print("\n" + "=" * 70)
    print("SPECIAL ANALYSIS: Path 12")
    print("=" * 70)

    path12_entry = [0b000, 0b000, 0b000, 0b110, 0b110, 0b000, 0b101, 0b011]

    print("\nPattern observation:")
    print("  Notice that ℓ_5 = 000 in Path 12 vs 101 in current")
    print("  This is exactly like setting ℓ_5 = ℓ_1 instead of using the formula")

    print("\n  What if we use: ℓ_w = rotL(G((w-1) | 1), 1, k) for certain w?")
    for w in range(8):
        idx_and = (w - 1) & ~1 if w > 0 else 0
        idx_or = (w - 1) | 1 if w > 0 else 0

        pred_and = rotl_bits(gray_code(idx_and), 1, k) if w > 0 else 0
        pred_or = rotl_bits(gray_code(idx_or), 1, k) if w > 0 else 0

        print(f"  w={w}: &~1 gives {bits_to_str(pred_and, k)}, |1 gives {bits_to_str(pred_or, k)}, "
              f"Path12={bits_to_str(path12_entry[w], k)}")
