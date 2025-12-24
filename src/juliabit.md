# C to Julia Cheat Sheet: Bitwise and Integer Operations

This cheat sheet covers the translation of C bitwise and integer operations to Julia, with special attention to pitfalls when porting Hilbert curve code.

---

## Critical Difference: XOR

**This is the most dangerous translation error!**

| Operation | C | Julia | Notes |
|-----------|---|-------|-------|
| Bitwise XOR | `a ^ b` | `a ⊻ b` or `xor(a, b)` | **C's `^` is exponentiation in Julia!** |
| Exponentiation | `pow(a, b)` | `a ^ b` | Julia's `^` is NOT XOR |

```c
// C
uint32_t x = a ^ b;  // XOR
```

```julia
# Julia
x = a ⊻ b      # XOR (using Unicode operator)
x = xor(a, b)  # XOR (using function)

# WRONG - this is exponentiation!
x = a ^ b      # This computes a raised to the power b
```

**Tip:** Type `\xor<TAB>` in Julia REPL or VS Code to get `⊻`.

---

## Bitwise Operators

| Operation | C | Julia | Example |
|-----------|---|-------|---------|
| AND | `a & b` | `a & b` | `0b1100 & 0b1010` → `0b1000` (8) |
| OR | `a \| b` | `a \| b` | `0b1100 \| 0b1010` → `0b1110` (14) |
| XOR | `a ^ b` | `a ⊻ b` or `xor(a, b)` | `0b1100 ⊻ 0b1010` → `0b0110` (6) |
| NOT | `~a` | `~a` | `~0b0000` → `-1` (all bits set) |
| NAND | `~(a & b)` | `nand(a, b)` or `a ⊼ b` | |
| NOR | `~(a \| b)` | `nor(a, b)` or `a ⊽ b` | |

---

## Bit Shifting

| Operation | C | Julia | Notes |
|-----------|---|-------|-------|
| Left shift | `a << n` | `a << n` | Same syntax |
| Right shift (arithmetic) | `a >> n` | `a >> n` | Preserves sign bit for signed types |
| Right shift (logical) | `(unsigned)a >> n` | `a >>> n` | Always fills with zeros |

```c
// C
int32_t x = -8 >> 2;           // Arithmetic: -2 (sign preserved)
uint32_t y = (uint32_t)-8 >> 2; // Logical: large positive number
```

```julia
# Julia
x = Int32(-8) >> 2    # Arithmetic: -2 (sign preserved)
y = Int32(-8) >>> 2   # Logical: 1073741822 (zeros filled in)
```

**Julia has built-in bit rotation:**

| Operation | C | Julia |
|-----------|---|-------|
| Rotate left by k | Custom function | `bitrotate(x, k)` |
| Rotate right by k | Custom function | `bitrotate(x, -k)` |

```c
// C - must write your own
uint32_t rotl(uint32_t x, int k, int bits) {
    k %= bits;
    return ((x << k) | (x >> (bits - k))) & ((1u << bits) - 1);
}
```

```julia
# Julia - built-in, but rotates full word width
bitrotate(x, k)   # Rotate left by k bits
bitrotate(x, -k)  # Rotate right by k bits

# For n-bit rotation (like in Hilbert code), still need custom:
function rotl_n(x::T, k, n) where T <: Integer
    mask = (one(T) << n) - one(T)
    x &= mask
    k = mod(k, n)
    k == 0 && return x
    return ((x << k) | (x >> (n - k))) & mask
end
```

---

## Integer Division and Modulo

| Operation | C | Julia | Notes |
|-----------|---|-------|-------|
| Truncated division | `a / b` (int) | `a ÷ b` or `div(a, b)` | Rounds toward zero |
| Floored division | `floor(a / b)` | `fld(a, b)` | Rounds toward -∞ |
| Ceiling division | `ceil(a / b)` | `cld(a, b)` | Rounds toward +∞ |
| Remainder (C-style) | `a % b` | `a % b` or `rem(a, b)` | Sign matches dividend |
| Modulo (math-style) | — | `mod(a, b)` | Sign matches divisor |

**Important for Hilbert code:** The `%` operator behaves the same for positive integers, but differs for negatives:

```c
// C
-7 % 3   // → -1 (sign of dividend)
```

```julia
# Julia
-7 % 3      # → -1 (rem, sign of dividend) - same as C
mod(-7, 3)  # → 2  (mod, sign of divisor) - different!
```

For the Hilbert curve code where all values are non-negative, `%` and `mod` are equivalent.

---

## Masks and Bit Manipulation

| Operation | C | Julia | Notes |
|-----------|---|-------|-------|
| Create n-bit mask | `(1u << n) - 1` | `(one(T) << n) - one(T)` | Use `one(T)` for type stability |
| Check bit k | `(x >> k) & 1` | `(x >> k) & 1` | Same |
| Set bit k | `x \| (1 << k)` | `x \| (1 << k)` | Same |
| Clear bit k | `x & ~(1 << k)` | `x & ~(1 << k)` | Same |
| Toggle bit k | `x ^ (1 << k)` | `x ⊻ (1 << k)` | **XOR difference!** |
| Count set bits | `__builtin_popcount(x)` | `count_ones(x)` | |
| Count trailing zeros | `__builtin_ctz(x)` | `trailing_zeros(x)` | |
| Count leading zeros | `__builtin_clz(x)` | `leading_zeros(x)` | |
| Count trailing ones | Custom loop | `trailing_ones(x)` | Julia has this built-in! |

---

## Type Considerations

| C Type | Julia Type | Notes |
|--------|------------|-------|
| `uint8_t` | `UInt8` | |
| `uint16_t` | `UInt16` | |
| `uint32_t` | `UInt32` | |
| `uint64_t` | `UInt64` | |
| `__uint128_t` | `UInt128` | Julia has native support |
| `int` | `Int` (alias for Int64 on 64-bit) | |
| Arbitrary | `BigInt` | Julia handles arbitrary precision natively |

**Type-stable mask creation:**

```c
// C
uint32_t mask = (1u << n) - 1;
```

```julia
# Julia - type stable
mask = (one(UInt32) << n) - one(UInt32)

# Or using type parameter
function make_mask(::Type{T}, n) where T <: Integer
    (one(T) << n) - one(T)
end
```

---

## Hilbert Code Translation Examples

### Gray Code

```c
// C
uint32_t gray_code(uint32_t i) {
    return i ^ (i >> 1);
}
```

```julia
# Julia
gray_code(i) = i ⊻ (i >> 1)
```

### Gray Decode

```c
// C
uint32_t gray_decode(uint32_t g) {
    uint32_t i = 0;
    while (g) {
        i ^= g;
        g >>= 1;
    }
    return i;
}
```

```julia
# Julia - direct translation
function gray_decode(g)
    i = zero(g)
    while g != 0
        i ⊻= g
        g >>= 1
    end
    return i
end

# Julia - elegant alternative using bit manipulation
function gray_decode(g::T) where T <: Integer
    i = g
    shift = 1
    while shift < sizeof(T) * 8
        i ⊻= i >> shift
        shift <<= 1
    end
    return i
end
```

### Trailing Ones (for Hamilton's d sequence)

```c
// C
int trailing_ones(uint32_t i) {
    int c = 0;
    while (i & 1) {
        c++;
        i >>= 1;
    }
    return c;
}
```

```julia
# Julia - built-in!
trailing_ones(i)
```

### T-Transform

```c
// C
uint32_t T_transform(uint32_t e, int d, int bits, uint32_t b) {
    return rrotate((b ^ e) & mask_bits(bits), (d + 1) % bits, bits);
}
```

```julia
# Julia
function T_transform(e, d, bits, b)
    masked = (b ⊻ e) & mask_bits(bits)
    return rotr_n(masked, (d + 1) % bits, bits)
end
```

---

## Operator Precedence Comparison

Both C and Julia have similar precedence for bitwise operators, but be careful:

| Precedence (high to low) | C | Julia |
|--------------------------|---|-------|
| Unary | `~ !` | `~ !` |
| Shifts | `<< >>` | `<< >> >>>` |
| Comparison | `< > <= >=` | `< > <= >=` |
| Bitwise AND | `&` | `&` |
| Bitwise XOR | `^` | `⊻` |
| Bitwise OR | `\|` | `\|` |

**Tip:** When in doubt, use parentheses. The Hilbert code uses many compound expressions like `(b ^ e) & mask` — keep those parentheses in Julia.

---

## Quick Reference Card

```
C           Julia           Operation
─────────────────────────────────────────
a ^ b       a ⊻ b          XOR ← DANGER!
a ^ b       xor(a, b)      XOR (function form)
a ^ b       a ^ b          EXPONENTIATION in Julia!
a & b       a & b          AND
a | b       a | b          OR
~a          ~a             NOT
a << n      a << n         Left shift
a >> n      a >> n         Arithmetic right shift
(uint)a>>n  a >>> n        Logical right shift
—           bitrotate(a,k) Rotate left by k
a % b       a % b          Remainder (C-style sign)
a % b       mod(a, b)      Modulo (math-style sign)
a / b       a ÷ b          Integer division
(1<<n)-1    (1<<n)-1       n-bit mask (but use one(T) for type stability)
```

---

## Common Pitfalls Summary

1. **XOR is `⊻` not `^`** — The #1 source of bugs when porting from C
2. **Use `one(T)` for masks** — `1 << n` gives `Int64`; use `one(UInt32) << n` for type stability
3. **`>>>` for unsigned shift** — C casts to unsigned; Julia uses `>>>` operator
4. **Julia has `trailing_ones`** — No need to write a loop
5. **Julia has `bitrotate`** — But it rotates full word width, not n-bit
6. **`mod` vs `%`** — Same for positive numbers, different for negative
