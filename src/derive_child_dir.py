#!/usr/bin/env python3
"""
Derive closed-form formulas for alternative child_dir functions.
"""

def trailing_ones(w):
    count = 0
    while (w & 1) != 0:
        count += 1
        w >>= 1
    return count

def bits_to_str(x, k):
    return format(x, f'0{k}b')

def current_child_dir(w, k):
    """Current implementation."""
    if w == 0:
        return 1
    if w & 1:  # odd
        return (trailing_ones(w) + 1) % k
    else:  # even
        return (trailing_ones(w - 1) + 1) % k

def test_child_dir_formula(name, directions, k):
    """Try to find closed form for child_dir."""
    print(f"\n{'='*70}")
    print(f"Finding child_dir formula for: {name}")
    print(f"{'='*70}")

    n = len(directions)
    print(f"Target a_w: {directions}")
    current = [current_child_dir(w, k) for w in range(n)]
    print(f"Current a_w: {current}")

    # Find differences
    diffs = [(w, directions[w], current[w]) for w in range(n) if directions[w] != current[w]]

    if not diffs:
        print("✓ Matches current implementation exactly!")
        return

    print(f"\nDifferences at {len(diffs)} position(s):")
    for w, alt, cur in diffs:
        print(f"  w={w}: alternative={alt}, current={cur}")

    # Try conditional formulas
    print(f"\nTrying conditional formulas...")

    # Simple swap at specific w
    for swap_w, alt_val, cur_val in diffs:
        formula_works = True
        formula = f"if w == {swap_w}: return {alt_val}; else: use current formula"

        for w in range(n):
            if w == swap_w:
                pred = alt_val
            else:
                pred = current_child_dir(w, k)

            if pred != directions[w]:
                formula_works = False
                break

        if formula_works:
            print(f"  ✓ Works: {formula}")

    # Try XOR/swap patterns
    if len(diffs) == 2 and diffs[0][0] + 1 == diffs[1][0]:
        # Two consecutive positions
        w1, alt1, cur1 = diffs[0]
        w2, alt2, cur2 = diffs[1]

        if alt1 == cur2 and alt2 == cur1:
            print(f"\n  Pattern detected: values at w={w1} and w={w2} are SWAPPED")
            print(f"    w={w1}: current={cur1} → alternative={alt1} (which is current[{w2}])")
            print(f"    w={w2}: current={cur2} → alternative={alt2} (which is current[{w1}])")

            # Try to express this as a closed form
            print(f"\n  Possible formula:")
            print(f"    a_w = current_child_dir(w ⊕ δ(w), k)")
            print(f"    where δ(w) = 1 if w ∈ {{{w1}, {w2}}} else 0")

    # Try to find bit-pattern based formula
    print(f"\nLooking for bit patterns in differences...")
    diff_positions = [w for w, _, _ in diffs]
    print(f"  Positions with differences: {diff_positions}")
    print(f"  In binary: {[bits_to_str(w, k) for w in diff_positions]}")

    # Check if there's a simple bit test
    if len(diffs) == 1:
        w_diff = diffs[0][0]
        print(f"\n  Single difference at w={w_diff} = {bits_to_str(w_diff, k)}")
        print(f"    Could use: if w == {w_diff}: return {diffs[0][1]}; else: current_formula")

    # Try modular arithmetic
    print(f"\nChecking modular patterns...")
    for mod in [2, 4, 8]:
        residues = {}
        for w, alt, _ in diffs:
            residue = w % mod
            if residue not in residues:
                residues[residue] = []
            residues[residue].append((w, alt))

        if len(residues) == 1:
            res = list(residues.keys())[0]
            print(f"  All differences occur when w ≡ {res} (mod {mod})")

if __name__ == "__main__":
    k = 3

    # Test alternative child_dir sequences
    alternatives = {
        "Path 5": [1, 2, 0, 2, 0, 2, 2],
        "Path 9": [1, 2, 2, 0, 0, 2, 0],
        "Path 12": [1, 2, 2, 0, 2, 0, 2],
        "Path 1": [1, 2, 0, 1, 1, 0, 0],
    }

    for name, dirs in alternatives.items():
        test_child_dir_formula(name, dirs, k)

    # Now write out complete formulas
    print(f"\n{'='*70}")
    print("SUMMARY: Complete Alternative Formulas")
    print(f"{'='*70}")

    print("""
Path 12 (simplest - only differs at w=5):
─────────────────────────────────────────
child_entry(w, k):
  if w == 0: return 0
  if w == 5: return 0b000  // Special case!
  else: return rotL(G((w-1) & ~1), 1, k)

  Equivalently:
  if w == 0: return 0
  else: return rotL(G((w-1) & ~1), 1, k) ⊕ (0b101 if w == 5 else 0)

child_dir(w, k):
  if w == 4: return 2  // Instead of 0
  if w == 5: return 0  // Instead of 2
  else: use current formula

  Notice: w=4 and w=5 have their values SWAPPED!
    """)

    print("""
Path 5 (differs at w=3):
────────────────────────
child_entry(w, k):
  if w == 0: return 0
  else: return rotL(G((w-1) & ~1), 1, k) ⊕ (0b101 if w == 3 else 0)

child_dir(w, k):
  if w == 2: return 0  // Instead of 2
  if w == 3: return 2  // Instead of 0
  else: use current formula

  Notice: w=2 and w=3 have their values SWAPPED!
    """)

    print("""
Path 9 (differs at w=7):
────────────────────────
child_entry(w, k):
  if w == 0: return 0
  else: return rotL(G((w-1) & ~1), 1, k) ⊕ (0b101 if w == 7 else 0)

child_dir(w, k):
  if w == 6: return 0  // Instead of 2
  else: use current formula
    """)
