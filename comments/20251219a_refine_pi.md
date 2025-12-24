# Hilbert Curves via Affine Maps with Explicit Permutations

This document reformulates the Hilbert curve algorithm using states of the form $(e, \pi)$ where:
- $e \in V(A)$ is a translation (bitvector)
- $\pi \in \mathrm{Sym}(A)$ is a permutation of axis labels

The key insight: **carry the permutation itself, not an index into a family of permutations**. This eliminates the $d+1$ artifacts and makes the anisotropic embedding story natural.

---

## 0. Notation and conventions

| Symbol | Meaning |
|--------|---------|
| $A$ | Set of axis labels $\{0, 1, \ldots, n-1\}$ |
| $V(A) = \mathrm{GF}(2)^A$ | Bitvectors indexed by axis labels |
| $\mathrm{Sym}(A)$ | Permutations of axis labels |
| $+$ | XOR (addition in $\mathrm{GF}(2)$) |
| $\circ$ | Function/permutation composition (left-to-right: $f \circ g$ means "apply $g$ first") |

---

## 1. Permutations act on bitvectors

### 1.1 The action

A permutation $\pi \in \mathrm{Sym}(A)$ acts on a bitvector $v \in V(A)$ by relabeling coordinates:
$$
(\pi \cdot v)(a) := v(\pi^{-1}(a))
$$

**In words:** The value at position $a$ in the result comes from position $\pi^{-1}(a)$ in the input.

**Why $\pi^{-1}$?** This makes the action a *left* action: $(\pi_1 \circ \pi_2) \cdot v = \pi_1 \cdot (\pi_2 \cdot v)$.

### 1.2 Key property: preserves adjacency

If $u + v = \mathbf{e}_a$ (differ in exactly bit $a$), then:
$$
(\pi \cdot u) + (\pi \cdot v) = \mathbf{e}_{\pi(a)}
$$

The difference moves to the relabeled axis. This is why orientation changes don't break Gray-code adjacency.

### 1.3 Cyclic permutations

Define the **right-shift** permutation $\sigma \in \mathrm{Sym}(A)$ by:
$$
\sigma(a) := (a + 1) \mod n
$$

Then $\sigma^k(a) = (a + k) \mod n$, and $\sigma^n = \mathrm{id}$.

For equal-sided Hilbert curves, $\pi$ is always a power of $\sigma$.

---

## 2. Affine maps on $V(A)$

### 2.1 Definition

An **affine map** is a function $S: V(A) \to V(A)$ of the form:
$$
S_{e,\pi}(v) := \pi \cdot v + e
$$

where $\pi \in \mathrm{Sym}(A)$ is the **linear part** and $e \in V(A)$ is the **translation**.

**Order:** First permute, then translate.

### 2.2 Composition

Let $S_1 = S_{e_1, \pi_1}$ and $S_2 = S_{e_2, \pi_2}$. Then:
$$
(S_1 \circ S_2)(v) = S_1(S_2(v)) = S_1(\pi_2 \cdot v + e_2) = \pi_1 \cdot (\pi_2 \cdot v + e_2) + e_1
$$
$$
= (\pi_1 \circ \pi_2) \cdot v + \pi_1 \cdot e_2 + e_1
$$

So composition is:
$$
\boxed{(e_1, \pi_1) \cdot (e_2, \pi_2) = (e_1 + \pi_1 \cdot e_2, \; \pi_1 \circ \pi_2)}
$$

This is the standard **semidirect product** $V(A) \rtimes \mathrm{Sym}(A)$.

### 2.3 Group structure

| Operation | Formula |
|-----------|---------|
| Identity | $(0, \mathrm{id})$ |
| Inverse | $(e, \pi)^{-1} = (\pi^{-1} \cdot e, \; \pi^{-1})$ |
| Composition | $(e_1, \pi_1) \cdot (e_2, \pi_2) = (e_1 + \pi_1 \cdot e_2, \; \pi_1 \circ \pi_2)$ |

**Verification of inverse:**
$(e, \pi) \cdot (\pi^{-1} \cdot e, \pi^{-1}) = (e + \pi \cdot (\pi^{-1} \cdot e), \pi \circ \pi^{-1}) = (e + e, \mathrm{id}) = (0, \mathrm{id})$ ✓

### 2.4 The inverse map

If $S_{e,\pi}(v) = \pi \cdot v + e$, then:
$$
S_{e,\pi}^{-1}(w) = \pi^{-1} \cdot (w + e)
$$

**Verification:** $S(S^{-1}(w)) = \pi \cdot (\pi^{-1} \cdot (w + e)) + e = (w + e) + e = w$ ✓

---

## 3. What is $\pi$, concretely?

### 3.1 For equal-sided Hilbert

For equal-sided Hilbert curves with $n$ axes, $\pi$ is always a **cyclic rotation** of axis labels:
$$
\pi = \sigma^{-r} \quad \text{for some } r \in \{0, 1, \ldots, n-1\}
$$

where $\sigma(a) = (a+1) \mod n$.

**Equivalently:** $\pi(a) = (a - r) \mod n$.

### 3.2 How to implement $\pi$

**Representation:** Store $r \in \{0, \ldots, n-1\}$ (the rotation index).

**Applying $\pi$ to a bitvector $v$:**
```
def apply_pi(v: bitvector, r: int, n: int) -> bitvector:
    result = 0
    for a in range(n):
        bit_value = (v >> ((a + r) % n)) & 1
        result |= bit_value << a
    return result
```

**Explanation:** $(\pi \cdot v)(a) = v(\pi^{-1}(a)) = v((a + r) \mod n)$.

**Composing two permutations:**
```
def compose_pi(r1: int, r2: int, n: int) -> int:
    return (r1 + r2) % n
```

**Inverse:**
```
def invert_pi(r: int, n: int) -> int:
    return (n - r) % n
```

### 3.3 Connection to Hamilton's $d$

Hamilton uses a "direction" parameter $d \in \mathbb{Z}_n$. The relationship is:
$$
r = d + 1 \pmod{n}
$$

In other words, $\pi = \sigma^{-(d+1)}$.

**This is why $d+1$ appears everywhere in Hamilton's formulas:** it's the rotation index we actually use. By storing $\pi$ (or equivalently $r$) directly, we eliminate the $+1$ offset.

---

## 4. The Hilbert state

### 4.1 State representation

The Hilbert algorithm's state at each level is an affine map:
$$
S = S_{e, \pi}
$$

where:
- $e \in V(A)$ is the **entry translation** (which corner we enter at)
- $\pi \in \mathrm{Sym}(A)$ is the **axis permutation** (how axes are reordered)

### 4.2 Initial state

The initial state is:
$$
S_0 = (0, \sigma^{-1})
$$

Or in terms of the rotation index: $e = 0$, $r = 1$.

**Meaning:** We start at corner $0$, with axes rotated by $1$ position.

### 4.3 Per-level bijection

At each level with state $(e, \pi)$, the bijection between **digits** $w$ and **plane labels** $\ell$ is:

**Decoding (digit → label):**
$$
\ell = S_{e,\pi}(G(w)) = \pi \cdot G(w) + e
$$

**Encoding (label → digit):**
$$
w = G^{-1}(S_{e,\pi}^{-1}(\ell)) = G^{-1}(\pi^{-1} \cdot (\ell + e))
$$

where $G$ is the Gray code operator.

---

## 5. The generator $\mu$

### 5.1 Definition

The **generator** $\mu: \{0, \ldots, 2^n - 1\} \to V(A) \rtimes \mathrm{Sym}(A)$ maps each child index (digit) to its relative orientation:
$$
\mu(w) = (e(w), \pi(w))
$$

### 5.2 Explicit formulas

Using Hamilton's entry-point function $e_H(w)$ and direction function $d(w)$:
$$
e(w) = e_H(w)
$$
$$
\pi(w) = \sigma^{-(d(w) + 1)}
$$

Or in terms of rotation index: $r(w) = d(w) + 1 \pmod{n}$.

**Hamilton's formulas for reference:**
- Entry: $e_H(0) = 0$; for $w > 0$: $e_H(w) = G(b(2\lfloor(w-1)/2\rfloor))$
- Direction: $d(0) = 0$; for $w > 0$:
  - $d(w) = \mathrm{tsb}(w-1) \mod n$ if $w$ even
  - $d(w) = \mathrm{tsb}(w) \mod n$ if $w$ odd

where $\mathrm{tsb}(i)$ counts trailing set bits.

### 5.3 State update

After processing child $w$, the state updates by composition:
$$
S' = S \cdot \mu(w) = (e, \pi) \cdot (e(w), \pi(w)) = (e + \pi \cdot e(w), \; \pi \circ \pi(w))
$$

Explicitly:
- New translation: $e' = e + \pi \cdot e(w)$
- New permutation: $\pi' = \pi \circ \pi(w)$

In terms of rotation indices:
- $r' = r + r(w) \pmod{n}$

### 5.4 Why this is cleaner

**Old way (Hamilton):**
- State: $(e_H, d)$
- Update: $e'_H = e_H + \rho^{-(d+1)} \cdot e_H(w)$, $d' = d + d(w) + 1$
- Every formula has $d+1$ or $\rho^{-(d+1)}$

**New way:**
- State: $(e, \pi)$ or $(e, r)$
- Update: $e' = e + \pi \cdot e(w)$, $\pi' = \pi \circ \pi(w)$
- Or: $e' = e + \mathrm{apply\_pi}(e(w), r)$, $r' = r + r(w)$
- The permutation/rotation IS the thing we carry, not an index-minus-one into it

---

## 6. Decode algorithm

Given index $h$, compute point $p$.

```
decode(h, n, m):
    # Extract digits (MSB first)
    W = digits_base_2n(h, m)  # W[0] is MSB

    # Initial state
    e = 0
    r = 1  # rotation index

    # Process each level
    for i in 0 to m-1:
        # Compute plane label
        g = gray_code(W[i])
        ℓ[i] = apply_pi(g, r, n) XOR e

        # Update state
        e_child, r_child = mu(W[i])
        e = e XOR apply_pi(e_child, r, n)
        r = (r + r_child) mod n

    # Scatter plane labels to coordinates
    p = scatter(ℓ, m, n)
    return p
```

### 6.1 Parallel version

The state updates form a scan:
1. **Map:** $M[i] = \mu(W[i])$
2. **Scan:** $S[i] = S[0] \cdot M[0] \cdot M[1] \cdots M[i-1]$
3. **Map:** $\ell[i] = S[i](G(W[i]))$

Depth: $O(\log m)$ for the scan, $O(1)$ for the maps.

---

## 7. Encode algorithm

Given point $p$, compute index $h$.

```
encode(p, n, m):
    # Gather plane labels
    ℓ = gather(p, m, n)

    # Initial state
    e = 0
    r = 1

    # Process each level
    for i in 0 to m-1:
        # Invert the affine map
        temp = ℓ[i] XOR e
        g = apply_pi(temp, (n - r) mod n, n)  # apply π^{-1}
        W[i] = inverse_gray_code(g)

        # Update state
        e_child, r_child = mu(W[i])
        e = e XOR apply_pi(e_child, r, n)
        r = (r + r_child) mod n

    # Pack digits
    h = pack_base_2n(W)
    return h
```

### 7.1 Parallel version (function tables)

The sequential dependency can be broken using function composition:

1. **Build transition tables:** For each plane label $\ell$, build the function $f_\ell: (e, r) \mapsto (e', r')$.
2. **Parallel scan:** Compose the functions.
3. **Evaluate:** Apply composed functions to get all states.
4. **Extract digits:** Invert each $\ell$ using its state.

Table size: $|V(A)| \times |\mathbb{Z}_n| = 2^n \times n$ entries per level.

---

## 8. Proof sketch

### 8.1 Encode/decode are inverses

Both directions use the same sequence of states $(e_i, \pi_i)$, computed from the same digit sequence via the same scan. The per-level bijection $G$ and $S_{e,\pi}$ are invertible. Done.

### 8.2 Lattice continuity

Key facts:
1. $G(w)$ and $G(w+1)$ differ in one bit (Gray code property)
2. Affine maps preserve one-bit differences (§2)
3. The generator $\mu$ satisfies gluing conditions: exit of child $w$ is adjacent to entry of child $w+1$

Therefore, incrementing $h$ by 1 produces a point differing by 1 in exactly one coordinate.

---

## 9. The anisotropic case

When axes have different precisions, the active axis set $A_s$ changes with level $s$.

### 9.1 What changes

- The permutation $\pi$ acts on $A_s$, not on all of $A$
- State is $(e, \pi)$ where $e \in V(A_s)$ and $\pi \in \mathrm{Sym}(A_s)$
- When $A_{s-1} \supset A_s$ (new axes activate), we embed the state

### 9.2 The embedding rule

Given state $(e, \pi)$ on $A_s$, embed to $A_{s-1}$ by:
1. **Extend $e$:** Set new axis bits to 0
2. **Extend $\pi$:** Act as identity on new axes

**Why this works:** The embedding preserves physical axis labels. A rotation of $\{1, 3, 5\}$ that sends $1 \mapsto 3 \mapsto 5 \mapsto 1$ becomes a rotation of $\{0, 1, 3, 5\}$ that sends $1 \mapsto 3 \mapsto 5 \mapsto 1$ and $0 \mapsto 0$.

### 9.3 Why $(e, \pi)$ is better than $(e, d)$

With $(e, d)$:
- $d$ is an index into the ordered active list
- When the list grows, you must "reindex" $d$ to preserve the physical axis
- This is error-prone (the original Hamilton paper got it wrong)

With $(e, \pi)$:
- $\pi$ is a permutation of physical axis labels
- Extending $\pi$ to more axes is trivial: just don't move the new ones
- The embedding is obvious and hard to get wrong

---

## 10. Summary

| Aspect | Hamilton $(e, d)$ | This document $(e, \pi)$ |
|--------|-------------------|--------------------------|
| State | Bitvector + integer mod $n$ | Bitvector + permutation |
| Transform | $\rho^{d+1}(v + e)$ | $\pi \cdot v + e$ |
| Composition | Involves $\rho^{-(d+1)}$ | Standard semidirect product |
| Offset artifacts | $d+1$ everywhere | None |
| Anisotropic embedding | "Reindex $d$" | "Extend $\pi$ by identity" |
| Implementation | Store integer $d$, compute $d+1$ | Store integer $r = d+1$ directly |

The permutation $\pi$ is the natural object. For equal-sided Hilbert, it happens to always be a cyclic rotation $\sigma^{-r}$, which we can represent as an integer $r$. But conceptually, we're carrying a permutation that tells us how to relabel axes—and that's exactly what the algorithm needs.
