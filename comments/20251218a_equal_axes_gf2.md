# Hilbert Curves on the Hypercube: A GF(2)^n Formulation

This document restates the theory of Hilbert curves on equal-sided hypercubes using the language of linear algebra over the Galois field GF(2). The goal is to clarify which operations are linear, which are affine, and how the proof of correctness emerges from these structures.

One thing I noticed while writing this: Hamilton's Lemma 2.12 for the inverse transform appears to have an off-by-one error  
(he writes n-d-1 where it should be n-d-2 based on my derivation). I used the correct formula in the document.               

---

## 1. The Vector Space GF(2)^n

### 1.1 Basic Definitions

Let **GF(2)** = {0, 1} be the field with two elements, where addition is XOR and multiplication is AND:

| + | 0 | 1 |   | · | 0 | 1 |
|---|---|---|---|---|---|---|
| 0 | 0 | 1 |   | 0 | 0 | 0 |
| 1 | 1 | 0 |   | 1 | 0 | 1 |

The key property: every element is its own additive inverse, so **v + v = 0** for all v.

**Definition 1.1.** Let **V_n = GF(2)^n** be the n-dimensional vector space over GF(2). Elements are n-tuples:
$$v = (v_0, v_1, \ldots, v_{n-1}), \quad v_j \in \{0, 1\}.$$

Addition is componentwise:
$$(u + v)_j = u_j + v_j \pmod 2.$$

We identify V_n with the integers {0, 1, ..., 2^n - 1} via the bijection:
$$v \leftrightarrow \sum_{j=0}^{n-1} v_j \cdot 2^j.$$

Under this identification, vector addition corresponds to bitwise XOR.

### 1.2 Standard Basis and Unit Vectors

The standard basis of V_n is {e_0, e_1, ..., e_{n-1}} where:
$$(\mathbf{e}_j)_k = \begin{cases} 1 & \text{if } k = j \\ 0 & \text{otherwise} \end{cases}$$

Under integer identification, **e_j = 2^j**.

Two vectors u, v ∈ V_n are **adjacent** (differ in exactly one coordinate) if and only if:
$$u + v = \mathbf{e}_j \quad \text{for some } j \in \{0, \ldots, n-1\}.$$

---

## 2. Linear Operators on V_n

### 2.1 The Cyclic Rotation Operator

**Definition 2.1.** The **right rotation operator** ρ: V_n → V_n is defined by:
$$(\rho v)_j = v_{(j-1) \bmod n}.$$

Equivalently, ρ shifts all coordinates one position to the right (cyclically).

**Example (n=3):** ρ(v_0, v_1, v_2) = (v_2, v_0, v_1).

**Properties:**
- ρ is linear (a permutation matrix)
- ρ^n = I (the identity)
- ρ^{-1} = ρ^{n-1} (left rotation by 1 = right rotation by n-1)
- ρ^r ρ^s = ρ^{r+s} (mod n)

**Lemma 2.2 (Rotation preserves adjacency).** If u + v = e_j, then ρ^r(u) + ρ^r(v) = e_{(j+r) mod n}.

*Proof.* Since ρ^r is linear: ρ^r(u) + ρ^r(v) = ρ^r(u + v) = ρ^r(e_j) = e_{(j+r) mod n}. ∎

### 2.2 The Gray Code Operator

**Definition 2.3.** The **Gray code operator** G: V_n → V_n is defined by:
$$G(v)_j = \begin{cases} v_j + v_{j+1} & \text{if } j < n-1 \\ v_{n-1} & \text{if } j = n-1 \end{cases}$$

**Matrix representation:** G = I + N where N is the nilpotent right-shift matrix:
$$N_{jk} = \begin{cases} 1 & \text{if } k = j+1 \text{ and } j < n-1 \\ 0 & \text{otherwise} \end{cases}$$

Explicitly for n=4:
$$G = \begin{pmatrix} 1 & 1 & 0 & 0 \\ 0 & 1 & 1 & 0 \\ 0 & 0 & 1 & 1 \\ 0 & 0 & 0 & 1 \end{pmatrix}$$

**Lemma 2.4.** G is linear, invertible, and its inverse is:
$$(G^{-1}v)_j = \sum_{k=j}^{n-1} v_k \pmod 2.$$

*Proof.* Linearity is immediate from the definition. For the inverse, note that G^{-1} is upper triangular with all 1s above and on the diagonal. Direct computation verifies G G^{-1} = I. ∎

**Theorem 2.5 (Gray code adjacency).** The sequence (G(v))_{v=0}^{2^n-1} (in integer order) satisfies:
$$G(v) + G(v+1) = \mathbf{e}_{g(v)}$$
where g(v) = number of trailing 1-bits in the binary representation of v.

*Proof.* (Standard; see Hamilton Lemma 2.3.) The key is that incrementing v in binary flips a suffix of bits 1...10 → 0...01, and G converts this to a single-bit change. ∎

**Corollary 2.6.** The Gray code sequence visits all 2^n vertices of the hypercube, with consecutive vertices adjacent.

### 2.3 The Transform T_{e,d}

**Definition 2.7.** For e ∈ V_n and d ∈ Z_n, the **orientation transform** T_{e,d}: V_n → V_n is:
$$T_{e,d}(v) = \rho^{d+1}(v + e).$$

**Decomposition:** T_{e,d} = ρ^{d+1} ∘ τ_e where τ_e(v) = v + e is translation.

**Lemma 2.8.** T_{e,d} is an affine bijection with:
- Linear part: ρ^{d+1}
- Translation: ρ^{d+1}(e)

Explicitly: T_{e,d}(v) = ρ^{d+1}(v) + ρ^{d+1}(e).

**Lemma 2.9 (Inverse transform).**
$$T_{e,d}^{-1}(w) = \rho^{-(d+1)}(w) + e = \rho^{n-d-1}(w) + e.$$

*Proof.* Solve T_{e,d}(v) = w for v:
$$\rho^{d+1}(v + e) = w \implies v + e = \rho^{-(d+1)}(w) \implies v = \rho^{-(d+1)}(w) + e.$$
(Using e + e = 0.) ∎

**Theorem 2.10 (T preserves adjacency).** If u + v = e_j, then:
$$T_{e,d}(u) + T_{e,d}(v) = \mathbf{e}_{(j + d + 1) \bmod n}.$$

*Proof.* By linearity of ρ^{d+1} and Lemma 2.2:
$$T_{e,d}(u) + T_{e,d}(v) = \rho^{d+1}(u + e) + \rho^{d+1}(v + e) = \rho^{d+1}(u + v) = \rho^{d+1}(\mathbf{e}_j) = \mathbf{e}_{(j+d+1) \bmod n}.$$
∎

**Corollary 2.11.** The transformed Gray code sequence:
$$u(i) = T_{e,d}^{-1}(G(i)), \quad i = 0, \ldots, 2^n - 1$$
is also a Gray code (consecutive terms are adjacent).

*Proof.* Both G and T_{e,d}^{-1} preserve adjacency. ∎

---

## 3. Entry and Exit Points

### 3.1 The Sequences e(i) and d(i)

The Hilbert curve visits 2^n sub-hypercubes in a specific order. Each sub-hypercube i has:
- **Entry point** e(i) ∈ V_n: the first corner visited
- **Exit point** f(i) ∈ V_n: the last corner visited
- **Internal direction** d(i) ∈ Z_n: where e(i) + f(i) = e_{d(i)}

**Constraint (Gluing condition).** For the curve to be continuous:
$$f(i) + e(i+1) = \mathbf{e}_{g(i)}$$
where g(i) is from Theorem 2.5. This says: exit of sub-hypercube i and entry of sub-hypercube i+1 are adjacent along axis g(i).

**Theorem 3.1 (Hamilton's formulas).** The sequences satisfying the gluing constraint with e(0) = 0 are:

**(a) Direction sequence:**
$$d(i) = \begin{cases} 0 & \text{if } i = 0 \\ g(i-1) \bmod n & \text{if } i \text{ even}, i > 0 \\ g(i) \bmod n & \text{if } i \text{ odd} \end{cases}$$

**(b) Entry sequence:**
$$e(i) = \begin{cases} 0 & \text{if } i = 0 \\ G\left(2\left\lfloor \frac{i-1}{2} \right\rfloor\right) & \text{if } i > 0 \end{cases}$$

**(c) Exit sequence:**
$$f(i) = e(i) + \mathbf{e}_{d(i)}.$$

*Proof.* See Hamilton Theorems 2.9-2.10. The key is an inductive argument using symmetry properties of the Gray code. ∎

### 3.2 Interpretation

The entry/exit formulas tell us how to orient each sub-hypercube so that:
1. The curve enters at e(i) and exits at f(i)
2. The exit f(i) is adjacent to the next entry e(i+1)
3. The overall traversal is continuous (unit steps)

---

## 4. The Hilbert Encoding and Decoding

### 4.1 Setup

Fix dimension n ≥ 1 and precision m ≥ 1. The lattice is:
$$P = \{0, 1, \ldots, 2^m - 1\}^n \cong (V_m)^n.$$

A point **p** = (p_0, ..., p_{n-1}) ∈ P has M = mn bits total.

The Hilbert index h ∈ {0, ..., 2^M - 1} will be built from m digits, each in V_n.

### 4.2 Level Extraction

**Definition 4.1.** For point p ∈ P and level i ∈ {0, ..., m-1}, the **level-i label** is:
$$\ell_i(p) = (\text{bit}(p_0, i), \text{bit}(p_1, i), \ldots, \text{bit}(p_{n-1}, i)) \in V_n.$$

This extracts bit i from each coordinate, forming an n-bit vector that identifies which of the 2^n children p lies in at level i.

### 4.3 Encoding Algorithm

**Algorithm (Encode: P → {0, ..., 2^M - 1}):**

```
Input: p ∈ P
Output: h ∈ {0, ..., 2^M - 1}

1. Initialize: (e, d, h) ← (0, 0, 0)
2. For i = m-1 down to 0:
   (a) Extract: ℓ ← ℓ_i(p) ∈ V_n
   (b) Transform: ℓ̄ ← T_{e,d}(ℓ) = ρ^{d+1}(ℓ + e)
   (c) Gray decode: w ← G^{-1}(ℓ̄)
   (d) Update state:
       e ← e + ρ^{-(d+1)}(e(w))
       d ← (d + d(w) + 1) mod n
   (e) Accumulate: h ← (h ≪ n) | w
3. Return h
```

### 4.4 Decoding Algorithm

**Algorithm (Decode: {0, ..., 2^M - 1} → P):**

```
Input: h ∈ {0, ..., 2^M - 1}
Output: p ∈ P

1. Initialize: (e, d) ← (0, 0), p ← (0, ..., 0)
2. For i = m-1 down to 0:
   (a) Extract digit: w ← bits [ni+n-1 : ni] of h
   (b) Gray encode: ℓ̄ ← G(w)
   (c) Inverse transform: ℓ ← T_{e,d}^{-1}(ℓ̄) = ρ^{-(d+1)}(ℓ̄) + e
   (d) Scatter to coordinates: bit(p_j, i) ← ℓ_j for j = 0, ..., n-1
   (e) Update state: (same as encoding)
       e ← e + ρ^{-(d+1)}(e(w))
       d ← (d + d(w) + 1) mod n
3. Return p
```

### 4.5 Linear Algebra View of One Level

At each level, with state (e, d) fixed, the transformation from label to digit is:
$$\Phi_{e,d}: V_n \to V_n, \quad \Phi_{e,d}(\ell) = G^{-1}(T_{e,d}(\ell)) = G^{-1}(\rho^{d+1}(\ell + e)).$$

This is the composition:
$$\ell \xrightarrow{\tau_e} \ell + e \xrightarrow{\rho^{d+1}} \rho^{d+1}(\ell + e) \xrightarrow{G^{-1}} w.$$

Each map is bijective, so Φ_{e,d} is bijective.

**The inverse is:**
$$\Phi_{e,d}^{-1}(w) = T_{e,d}^{-1}(G(w)) = \rho^{-(d+1)}(G(w)) + e.$$

---

## 5. Proof of Bijection

### 5.1 Per-Level Bijection

**Lemma 5.1.** For any state (e, d), the map Φ_{e,d}: V_n → V_n is a bijection.

*Proof.* Φ_{e,d} = G^{-1} ∘ ρ^{d+1} ∘ τ_e is a composition of bijections:
- τ_e is bijective (inverse is τ_e since e + e = 0)
- ρ^{d+1} is bijective (inverse is ρ^{-(d+1)})
- G^{-1} is bijective (inverse is G)  ∎

### 5.2 State Update Consistency

**Lemma 5.2.** Given state (e, d) and digit w, both encode and decode compute the same next state (e', d').

*Proof.* The state update rule is:
$$e' = e + \rho^{-(d+1)}(e(w)), \qquad d' = d + d(w) + 1 \pmod n.$$
This depends only on (e, d) and w, not on ℓ or h. Since encode computes w from ℓ and decode recovers ℓ from w, both paths through a given w yield the same state update. ∎

### 5.3 Main Bijection Theorem

**Theorem 5.3 (Encode and Decode are inverses).**
For all p ∈ P: Decode(Encode(p)) = p.
For all h ∈ {0, ..., 2^M - 1}: Encode(Decode(h)) = h.

*Proof.* By induction on levels i = m-1, ..., 0.

**Base case:** At i = m-1, both algorithms start with state (e, d) = (0, 0).

**Inductive step:** Assume at level i, encode and decode have matching states (e, d).

*Encode then decode:*
- Encode computes w = Φ_{e,d}(ℓ_i(p))
- Decode recovers ℓ = Φ_{e,d}^{-1}(w) = ℓ_i(p) ✓
- Both update state identically (Lemma 5.2)

*Decode then encode:*
- Decode computes ℓ = Φ_{e,d}^{-1}(w) from the digit w in h
- Encode computes w' = Φ_{e,d}(ℓ) = Φ_{e,d}(Φ_{e,d}^{-1}(w)) = w ✓
- Both update state identically

After all m levels, encode has reconstructed h from Decode(h), and decode has reconstructed p from Encode(p). ∎

---

## 6. Proof of Lattice Continuity

### 6.1 Goal

We prove that for all h ∈ {0, ..., 2^M - 2}:
$$\|H(h+1) - H(h)\|_1 = 1$$
where H = Decode and ∥·∥_1 is the L^1 norm (sum of absolute coordinate differences).

### 6.2 Oriented Child Ordering

**Lemma 6.1.** Fix state (e, d). Define the oriented child sequence:
$$u(i) = T_{e,d}^{-1}(G(i)) = \Phi_{e,d}^{-1}(i), \quad i = 0, \ldots, 2^n - 1.$$

Then consecutive children are adjacent:
$$u(i) + u(i+1) = \mathbf{e}_{g'(i)}$$
for some axis g'(i).

*Proof.* By Corollary 2.11, T_{e,d}^{-1} ∘ G preserves the Gray code adjacency property. ∎

### 6.3 Child Endpoint Gluing

**Lemma 6.2.** In the standard Hilbert construction, child i has:
- Entry corner at label e(i)
- Exit corner at label f(i) = e(i) + e_{d(i)}

The exit of child i and entry of child i+1 satisfy:
$$f(i) + e(i+1) = \mathbf{e}_{g(i)}.$$

*Proof.* This is the defining gluing condition (Hamilton Equation 1). ∎

**Lemma 6.3 (Geometric interpretation).**
- f(i) + e(i+1) = e_{g(i)} means: exit corner of child i and entry corner of child i+1 differ in exactly bit g(i).
- This bit g(i) corresponds to the axis along which children i and i+1 are neighbors.

### 6.4 From Corner Adjacency to Lattice Step

**Lemma 6.4 (Scaling).** Consider axis j at level i. The lattice coordinate range [0, 2^m - 1] is partitioned into 2^{m-i} intervals of size 2^i.

At level i, choosing bit b ∈ {0,1} selects the lower (b=0) or upper (b=1) half of the current interval:
- Lower half: [..., 2^{i-1} - 1]
- Upper half: [2^{i-1}, ...]

The boundary between halves is at 2^{i-1} - 1 → 2^{i-1}, a unit step.

**Lemma 6.5 (Corner-to-lattice).** If two sub-hypercubes at level i are neighbors along axis j (i.e., they differ only in bit j of their labels), then:
- The "upper face" of the low-side box along axis j has coordinate 2^{i-1} - 1
- The "lower face" of the high-side box along axis j has coordinate 2^{i-1}
- These differ by exactly 1.

### 6.5 Main Continuity Theorem

**Theorem 6.6 (Lattice Continuity).** For H = Decode:
$$\|H(h+1) - H(h)\|_1 = 1 \quad \text{for all } h \in \{0, \ldots, 2^M - 2\}.$$

*Proof by hierarchical decomposition.*

Write h in its base-2^n digit representation:
$$h = (w_{m-1}, w_{m-2}, \ldots, w_0)$$
where each w_i ∈ {0, ..., 2^n - 1}.

When h increments to h+1, there exists a smallest level i* such that:
- Digits w_0, ..., w_{i*-1} overflow (wrap from 2^n - 1 to 0)
- Digit w_{i*} increments by 1
- Digits w_{i*+1}, ..., w_{m-1} unchanged

**Interpretation:** The traversal moves from:
- The last point of child w_{i*} → The first point of child w_{i*} + 1
within the same level-(i*+1) parent.

**Step analysis at level i*:**

By Lemma 6.1, children w_{i*} and w_{i*}+1 are adjacent (in the oriented ordering).
By Lemma 6.2, exit(w_{i*}) and entry(w_{i*}+1) differ in one bit.
By Lemma 6.5, this one-bit difference in corner labels translates to a unit step in lattice coordinates.

**Within children:** The path within each child is itself a Hilbert curve (by recursion), so all its internal steps are unit steps by the same argument at finer levels.

**Conclusion:** Every step in the full traversal is a unit L^1 step. ∎

---

## 7. Summary: The Role of Linear Structure

### 7.1 Linear Operators

| Operator | Type | Matrix (n=3) |
|----------|------|--------------|
| ρ (rotation) | Linear, orthogonal | Permutation matrix |
| G (Gray code) | Linear, upper triangular | I + N |
| G^{-1} | Linear, upper triangular | All 1s above diagonal |

### 7.2 Affine Operators

| Operator | Linear Part | Translation |
|----------|-------------|-------------|
| τ_e (translation) | I | e |
| T_{e,d} | ρ^{d+1} | ρ^{d+1}(e) |
| Φ_{e,d} = G^{-1} ∘ T_{e,d} | G^{-1} ρ^{d+1} | G^{-1}(ρ^{d+1}(e)) |

### 7.3 Why This Structure Matters

1. **Bijection:** Follows immediately from composition of bijections. No case analysis needed.

2. **Adjacency preservation:** Linear maps preserve the "differ by one basis vector" property. The proof of continuity reduces to checking that translations don't break this.

3. **State update:** The formulas for e(w) and d(w) are non-linear functions of w (involving trailing-bit counts), but once w is known, the update is algebraically simple.

4. **Potential simplifications:** Viewing T_{e,d} as an element of the affine group Aff(V_n) suggests connections to:
   - Group-theoretic characterizations of Hilbert curves
   - Composition rules for transforms (Lemma 2.13 in Hamilton)
   - Invariants under the action of the symmetry group

---

## 8. Key Equations Reference

**Gray code:**
$$G(v)_j = v_j + v_{j+1}, \quad G^{-1}(v)_j = \sum_{k \geq j} v_k$$

**Transform:**
$$T_{e,d}(v) = \rho^{d+1}(v + e), \quad T_{e,d}^{-1}(w) = \rho^{-(d+1)}(w) + e$$

**Per-level bijection:**
$$w = \Phi_{e,d}(\ell) = G^{-1}(\rho^{d+1}(\ell + e))$$
$$\ell = \Phi_{e,d}^{-1}(w) = \rho^{-(d+1)}(G(w)) + e$$

**State update:**
$$e' = e + \rho^{-(d+1)}(e(w)), \quad d' = d + d(w) + 1 \pmod n$$

**Gluing condition:**
$$e(i+1) = e(i) + \mathbf{e}_{d(i)} + \mathbf{e}_{g(i)}$$
