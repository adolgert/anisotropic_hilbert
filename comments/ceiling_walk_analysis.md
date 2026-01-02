# Analysis: The "Ceiling Walk" Formula is Incorrect

## The Proposed Formula (from 20260102a_phase_offset.md)

```c
ℓ'_w = ℓ_w ⊕ [2^(k-1) if w ∉ {2^(k-1)-1, 2^(k-1)} else 0]
```

**Claim:** This creates a valid alternative Hilbert curve for k ≥ 4.

**Reality:** This formula is **incorrect** for all k ≥ 3.

## Test Results

### For k=3:
- ✗ Initial condition violated: s_0 = 100 ≠ 0
- ✗ Multiple neighbor violations

### For k=4:
- ✗ Initial condition violated: s_0 ≠ 0
- ✗ Neighbor violations at transitions around midpoint

### For k=5:
- ✗ Initial condition violated: s_0 = 10000 ≠ 0
- ✗ Neighbor violations at w=14→15 and w=16→17 (Hamming distance = 2)

## Why It Fails

### Problem 1: Initial Condition Violation

At w=0:
- Standard: ℓ_0 = 00000...
- Ceiling Walk: ℓ_0 = 00000... ⊕ 10000... = 10000...
- Therefore: s_0 = h_0 ⊕ ℓ_0 = 00000 ⊕ 10000 = **10000 ≠ 0**

The constraint **requires s_0 = 0** (start at origin). The formula violates this immediately.

### Problem 2: Ceiling-Floor Discontinuities

The formula creates discontinuities at the midpoint boundary:

**Before midpoint (w < mid_left):**
- Bit k-1 is toggled → "on the ceiling"

**At midpoint (w = mid_left or mid_right):**
- Bit k-1 follows standard → "on the floor"

**After midpoint (w > mid_right):**
- Bit k-1 is toggled → "back on the ceiling"

### The Fatal Flaw

At transitions crossing the boundary (e.g., 14→15 or 16→17 for k=5):
- You need to flip **TWO** bits:
  1. One bit for the walk constraint (the a_w step)
  2. One bit to change ceiling/floor state (bit k-1)

But the neighbor constraint requires **Hamming distance = 1** (exactly one bit flip).

This is impossible! You can't satisfy both requirements simultaneously.

### Specific Example (k=5, w=14→15):

```
w=14: s_14 = 10110 (ceiling, bit 4 = 1)
w=15: s_15 = 00010 (floor, bit 4 = 0)

Difference: 10110 ⊕ 00010 = 10100
Hamming distance: 2 (bits 2 and 4 differ)

✗ VIOLATION: Need exactly 1 bit to differ
```

## What Actually Works

From exhaustive search of k=3, valid alternatives only modify **1-2 specific positions**, not nearly all positions:

### Valid Alternative Formulas:

**Path 12:**
```c
ℓ_w = rotL(G((w-1) & ~1), 1, k) ⊕ (w == 5 ? 0b101 : 0)
```
Changes only at w=5

**Path 5:**
```c
ℓ_w = rotL(G((w-1) & ~1), 1, k) ⊕ (w == 3 ? 0b101 : 0)
```
Changes only at w=3

**Path 9:**
```c
ℓ_w = rotL(G((w-1) & ~1), 1, k) ⊕ (w == 7 ? 0b101 : 0)
```
Changes only at w=7

All three:
- ✓ Satisfy s_0 = 0
- ✓ Maintain Hamming distance = 1 between all consecutive s_w values
- ✓ Satisfy the face constraint

## Why the Document's "Proof" Fails

The document acknowledges the problem in Case D:
> "Wait, is the jump from 'floor' to 'ceiling' valid here?"
> "**Correction:** The mask logic requires that we only stay on the floor for the blocks adjacent to the high-axis crossing."

But the "correction" doesn't fix the fundamental issue. The formula still:
1. Toggles at w=0 (violating s_0 = 0)
2. Creates Hamming distance 2 transitions at the boundaries

## Conclusion

The Ceiling Walk formula is **mathematically incorrect**. It violates fundamental constraints:
- Initial condition (s_0 = 0)
- Neighbor constraint (Hamming distance = 1)

The correct approach for finding alternative Hilbert curves is to:
1. Make **sparse, targeted modifications** at specific positions
2. Verify all three constraints:
   - s_0 = 0
   - s_{w+1} differs from s_w by exactly 1 bit
   - (s_{w+1})_{d_w} = 1 (face constraint)

The exhaustive search for k=3 found exactly 13 valid alternatives, all using minimal modifications to the standard formula.
