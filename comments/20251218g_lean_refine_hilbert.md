# The Hilbert Curve as a Group-Theoretic Scan

This document captures a refined algebraic formulation of Hilbert curves on hypercubes, using the language of GF(2) vector spaces and semidirect products. The key insight is that the "imperative loop" in classical Hilbert algorithms is actually a **scan** (prefix product) over a group, followed by embarrassingly parallel local operations.

---

## 1. Setting

**Dimension:** $n \geq 1$ (number of axes)
**Precision:** $m \geq 1$ (bits per axis)
**Lattice:** $P = \{0, 1, \ldots, 2^m - 1\}^n$ (the $n$-dimensional grid with $2^m$ points per axis)
**Index range:** $\{0, 1, \ldots, 2^{mn} - 1\}$ (the Hilbert indices)

---

## 2. The Vector Space $V_n = \text{GF}(2)^n$

Elements of $V_n$ are $n$-tuples over the two-element field:
$$v = (v_0, v_1, \ldots, v_{n-1}), \quad v_j \in \{0, 1\}$$

**Addition** is componentwise XOR: $(u + v)_j = u_j \oplus v_j$.

**Key property:** Every element is its own inverse: $v + v = 0$.

**Identification with integers:** $v \leftrightarrow \sum_{j=0}^{n-1} v_j \cdot 2^j$.

**Adjacency:** Two vectors are adjacent if they differ in exactly one coordinate:
$$u + v = \mathbf{e}_j \quad \text{for some standard basis vector } \mathbf{e}_j = 2^j$$

---

## 3. Linear Operators on $V_n$

### 3.1 Cyclic Rotation $\rho$

$$(\rho \, v)_j = v_{(j-1) \bmod n}$$

This is the **right rotation** (or right cyclic shift). It's a permutation matrix.

**Properties:**
- $\rho^n = I$ (identity)
- $\rho^{-1} = \rho^{n-1}$ (left rotation)
- Rotation preserves adjacency: if $u + v = \mathbf{e}_j$, then $\rho^r(u) + \rho^r(v) = \mathbf{e}_{(j+r) \bmod n}$

### 3.2 Gray Code $G$

$$G(v)_j = \begin{cases} v_j + v_{j+1} & j < n-1 \\ v_{n-1} & j = n-1 \end{cases}$$

This is an **upper bidiagonal** matrix: $G = I + N$ where $N$ is the nilpotent right-shift.

**Inverse:**
$$(G^{-1} v)_j = \sum_{k=j}^{n-1} v_k \pmod 2$$

This is the **upper triangular** matrix with all 1s above and on the diagonal.

**Key property:** The Gray code sequence $(G(0), G(1), \ldots, G(2^n-1))$ visits all vertices of the hypercube with consecutive vertices adjacent.

### 3.3 The Transform $T_{e,d}$

For $e \in V_n$ and $d \in \mathbb{Z}_n$, define:
$$T_{e,d}(v) = \rho^{d+1}(v + e)$$

This is an **affine** map (translation followed by rotation).

**Inverse:**
$$T_{e,d}^{-1}(w) = \rho^{-(d+1)}(w) + e$$

**Key property:** $T_{e,d}$ preserves adjacency. Therefore, $T_{e,d}^{-1} \circ G$ is also a Gray code (a reoriented traversal of the hypercube).

---

## 4. The Hilbert Group $\mathcal{H} = V_n \rtimes \mathbb{Z}_n$

### 4.1 Definition

The **Hilbert group** is the semidirect product of $V_n$ and $\mathbb{Z}_n$, where $\mathbb{Z}_n$ acts on $V_n$ by rotation.

**Elements:** Pairs $(e, \delta)$ where $e \in V_n$ and $\delta \in \mathbb{Z}_n$.

**Group operation:**
$$(e_1, \delta_1) \cdot (e_2, \delta_2) = (e_1 + \rho^{-\delta_1}(e_2), \; \delta_1 + \delta_2)$$

**Identity:** $(0, 0)$

**Inverse:** $(e, \delta)^{-1} = (\rho^{\delta}(e), \, -\delta)$

### 4.2 Connection to Algorithm State

In Hamilton's algorithm, the state is a pair $(e, d)$ where:
- $e$ is the "entry point" (a translation)
- $d$ is the "direction" (determines rotation amount)

The transform uses $\rho^{d+1}$, so we identify:
$$\text{algorithm state } (e, d) \;\longleftrightarrow\; \text{group element } (e, d+1)$$

**Initial state:** $(e, d) = (0, 0)$ corresponds to group element $(0, 1)$.

### 4.3 State Update as Group Multiplication

The algorithm's state update:
$$e' = e + \rho^{-(d+1)}(e(w)), \qquad d' = d + d(w) + 1 \pmod n$$

is exactly:
$$(e, d+1) \cdot (e(w), d(w)+1) = (e', d'+1)$$

where $(e(w), d(w)+1)$ is the **relative orientation** of child $w$.

---

## 5. The Generator $\mu: V_n \to \mathcal{H}$

### 5.1 Definition

The **generator** maps each digit $w \in \{0, \ldots, 2^n-1\}$ to the relative transformation it induces:
$$\mu(w) = (e(w), \; d(w) + 1)$$

where $e(w)$ and $d(w)$ are Hamilton's entry point and direction functions.

### 5.2 Hamilton's Formulas

**Entry points:**
$$e(w) = \begin{cases} 0 & w = 0 \\ G\left(2\left\lfloor \frac{w-1}{2} \right\rfloor\right) & w > 0 \end{cases}$$

**Directions:**
$$d(w) = \begin{cases} 0 & w = 0 \\ g(w-1) \bmod n & w > 0 \text{ even} \\ g(w) \bmod n & w \text{ odd} \end{cases}$$

where $g(i) = \text{tsb}(i)$ is the number of trailing 1-bits in $i$.

### 5.3 What $\mu$ Encodes

The generator $\mu$ encapsulates the **geometry** of the Hilbert curve:
- It satisfies the **gluing condition**: exit of child $i$ is adjacent to entry of child $i+1$
- It ensures the curve **starts at 0** and **exits at $\mathbf{e}_{n-1}$**

The specific form of $\mu$ distinguishes Hilbert curves from other space-filling curves.

---

## 6. The Per-Level Bijection $\Phi_{e,d}$

### 6.1 Definition

For fixed state $(e, d)$, the bijection between level labels and digits is:
$$\Phi_{e,d}(\ell) = G^{-1}(\rho^{d+1}(\ell + e)) = G^{-1}(T_{e,d}(\ell))$$

**Inverse:**
$$\Phi_{e,d}^{-1}(w) = \rho^{-(d+1)}(G(w)) + e = T_{e,d}^{-1}(G(w))$$

### 6.2 Decomposition

$$\Phi_{e,d} = G^{-1} \circ \rho^{d+1} \circ \tau_e$$

where $\tau_e(v) = v + e$ is translation. This is a composition of:
1. Translation by $e$ (affine)
2. Rotation by $d+1$ (linear)
3. Inverse Gray code (linear)

All three are bijections, so $\Phi_{e,d}$ is a bijection.

---

## 7. The Functional Algorithm

### 7.1 Key Insight: Loop $\to$ Scan

The imperative loop over levels is equivalent to:
1. **Map:** Convert digits to group elements via $\mu$
2. **Scan:** Compute prefix products to get all states
3. **Map:** Apply local bijection $\Phi$ or $\Phi^{-1}$ at each level

### 7.2 Decoding (Index $\to$ Point)

```
decode(h):
    # Extract digits from index
    W = [w_{m-1}, w_{m-2}, ..., w_0]  # MSB to LSB

    # Step 1: Map digits to relative transforms
    M = map(μ, W)

    # Step 2: Scan to get absolute states
    # S[i] = state used when processing W[i]
    S = scanl(·, (0, 1), M)
    # S has m+1 elements; we use S[0], ..., S[m-1]

    # Step 3: Apply inverse transform at each level
    L = zipWith(Φ⁻¹, S[0:m], W)

    # Step 4: Scatter level labels to coordinates
    for i in 0..m-1:
        for j in 0..n-1:
            bit(p_j, m-1-i) = L[i]_j

    return p
```

**Complexity:**
- Step 1: $O(m)$ parallel
- Step 2: $O(\log m)$ depth (parallel prefix)
- Step 3: $O(m)$ parallel
- Step 4: $O(mn)$ parallel

### 7.3 Encoding (Point $\to$ Index)

```
encode(p):
    # Gather level labels from coordinates
    for i in 0..m-1:
        L[i] = (bit(p_0, m-1-i), ..., bit(p_{n-1}, m-1-i))

    # Iterative: digit depends on previous state
    S[0] = (0, 1)
    for i in 0..m-1:
        W[i] = Φ_{S[i]}(L[i])
        S[i+1] = S[i] · μ(W[i])

    # Pack digits into index
    h = pack(W)
    return h
```

**Note:** Encoding has a **triangular dependency**—digit $W[i]$ depends on state $S[i]$, which depends on $W[0], \ldots, W[i-1]$. This is inherently sequential unless $\mu$ has additional structure.

### 7.4 Asymmetry

| Operation | Parallelizable? | Reason |
|-----------|-----------------|--------|
| Decoding  | Yes ($O(\log m)$ depth) | Digits known; scan then map |
| Encoding  | No (inherently sequential) | State depends on previous digits |

---

## 8. Why This Formulation Is Better

### 8.1 Separation of Concerns

| Component | Role | Mathematical Object |
|-----------|------|---------------------|
| Geometry | "How are children oriented?" | Generator $\mu: V_n \to \mathcal{H}$ |
| Algebra | "How do orientations compose?" | Group $\mathcal{H} = V_n \rtimes \mathbb{Z}_n$ |
| Structure | "How does recursion unfold?" | Scan (prefix product) |
| Local transform | "How to convert label ↔ digit?" | Bijection $\Phi_{e,d}$ |

### 8.2 Proof Simplification

| Property | Proof Method |
|----------|--------------|
| Encode/decode are inverses | $\Phi_{e,d}$ is bijection; states match |
| Lattice continuity | $\mu$ satisfies gluing; $\Phi^{-1} \circ G$ preserves adjacency |
| Correctness of scan | Associativity of group operation |

No reasoning about "loop invariants" or "mutable state"—just algebraic identities.

### 8.3 Parallelism

The scan formulation immediately reveals that decoding is parallelizable with $O(\log m)$ depth using standard parallel prefix algorithms (e.g., Blelloch scan).

---

## 9. Open Questions and Potential Improvements

### 9.1 Structure of $\mu$

The generator $\mu$ is currently a "lookup table" defined by Hamilton's formulas. But:

$$e(w) = G(2\lfloor (w-1)/2 \rfloor) \quad \text{(for } w > 0\text{)}$$

This involves the **Gray code** $G$! And $d(w)$ involves $\text{tsb}$ (trailing set bits), which is related to the Gray code derivative.

**Question:** Can $\mu$ be expressed as a composition of linear GF(2) operations plus a simple nonlinearity?

If so, we might be able to:
- Vectorize $\mu$ across all $2^n$ children
- Express the entire Hilbert encoding as a single linear map plus corrections
- Find closed-form expressions without case analysis

### 9.2 The Trailing Set Bits Function

The function $\text{tsb}: \mathbb{Z}_{\geq 0} \to \mathbb{Z}_{\geq 0}$ counts trailing 1-bits:
$$\text{tsb}(i) = \max\{k : 2^k - 1 \text{ divides } i+1\}$$

In GF(2) terms, this is related to the **nilpotency index** of $(v + \mathbf{1})$ where $\mathbf{1} = (1, 1, \ldots, 1)$.

**Question:** Is there a GF(2)-linear characterization of $\text{tsb}$?

### 9.3 Can Encoding Be Parallelized?

Encoding has triangular dependency: $W[i]$ depends on $L[0..i]$.

**Speculation:** If $\mu$ has a special structure (e.g., $\mu(w)$ depends only on certain bits of $w$), we might be able to:
- Compute partial states speculatively
- Use a different decomposition that breaks the dependency

**Alternative:** Accept sequential encoding but note that for many applications (database indexing, range queries), **decoding is the hot path**, and that's already parallel.

### 9.4 Higher-Dimensional Gray Code?

The Gray code $G: V_n \to V_n$ is a linear bijection on single vectors.

The Hilbert encoding operates on **sequences** of vectors: $(V_n)^m \to (V_n)^m$.

**Question:** Is there a "lifted" or "higher-dimensional" Gray code $\tilde{G}: (V_n)^m \to (V_n)^m$ such that:
$$\text{Hilbert encoding} = \tilde{G} \circ \text{(permutation)} \circ \text{(local maps)}$$

### 9.5 Tensor Product Structure

A point $p \in P$ can be viewed as an element of $V_m \otimes V_n$ (an $m \times n$ matrix of bits).

The Hilbert index $h$ also has $mn$ bits.

**Question:** Does the encoding respect any tensor structure? Is it a "twisted" tensor product related to the semidirect product $V_n \rtimes \mathbb{Z}_n$?

---

## 10. Summary

The classical Hilbert curve algorithm, when viewed through the lens of GF(2) linear algebra:

1. **State updates** form a **semidirect product group** $\mathcal{H} = V_n \rtimes \mathbb{Z}_n$

2. **The loop** is a **scan** (prefix product) over $\mathcal{H}$

3. **Per-level transforms** are **affine bijections** composed of rotation, translation, and Gray code

4. **Geometry** is encoded in the **generator** $\mu: V_n \to \mathcal{H}$, which satisfies gluing conditions

5. **Decoding is parallel** ($O(\log m)$ depth); **encoding is sequential** (triangular dependency)

The remaining frontier is understanding whether $\mu$ has exploitable structure that could simplify or further parallelize the encoding.
