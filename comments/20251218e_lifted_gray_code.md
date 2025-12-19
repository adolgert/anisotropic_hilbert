# The Lifted Gray Code: Structure and Non-Linearity

This document explores whether there exists a "lifted" Gray code $\tilde{G}: (V_n)^m \to (V_n)^m$ that elegantly captures the Hilbert curve transformation.

## 1. The Question

The standard Gray code $G: V_n \to V_n$ is a **linear** bijection (upper bidiagonal matrix $I + N$).

The Hilbert decoding operates on **sequences**: digits $(w_1, \ldots, w_m)$ map to level labels $(\ell_1, \ldots, \ell_m)$.

**Question:** Is there a "lifted" Gray code $\tilde{G}: (V_n)^m \to (V_n)^m$ such that Hilbert decoding factors as:
$$\text{decode} = \text{(scatter)} \circ \tilde{G} \circ \text{(gather)}$$

---

## 2. The Decoding Map Explicitly

For digit sequence $W = (w_m, \ldots, w_1)$ (MSB to LSB), decoding computes:

1. **State scan:** $S_k = \mu(w_m) \cdot \mu(w_{m-1}) \cdots \mu(w_{m-k+1})$ in group $\mathcal{H} = V_n \rtimes \mathbb{Z}_n$
2. **Level transform:** $\ell_{m-k+1} = T^{-1}_{S_k}(G(w_{m-k+1}))$

where $T^{-1}_{(e,\delta)}(u) = \rho^{-\delta}(u) + e$.

---

## 3. Worked Example: $n=2$, $m=2$

### 3.1 The Generator $\mu$ for $n=2$

| $w$ | $e(w)$ | $d(w)$ | $\mu(w) = (e(w), d(w)+1)$ | Is identity? |
|-----|--------|--------|---------------------------|--------------|
| 0   | 0      | 0      | $(0, 1)$                  | No           |
| 1   | 0      | 1      | $(0, 0)$                  | **Yes**      |
| 2   | 0      | 1      | $(0, 0)$                  | **Yes**      |
| 3   | 3      | 0      | $(3, 1)$                  | No           |

**Key observation:** Two of four children have $\mu(w) = \text{identity}$.

### 3.2 The Decoding Map

For $W = (w_2, w_1)$:

**Level 2:** (initial state $(0, 1)$)
$$\ell_2 = \rho^{-1}(G(w_2)) = \rho(G(w_2))$$

**Level 1:** (state depends on $w_2$)

| $w_2$ | State after level 2 | $\ell_1$ |
|-------|---------------------|----------|
| 0     | $(0, 1) \cdot (0, 1) = (0, 0)$ | $G(w_1)$ |
| 1     | $(0, 1) \cdot (0, 0) = (0, 1)$ | $\rho(G(w_1))$ |
| 2     | $(0, 1) \cdot (0, 0) = (0, 1)$ | $\rho(G(w_1))$ |
| 3     | $(0, 1) \cdot (3, 1) = (3, 0)$ | $G(w_1) + 3$ |

### 3.3 The Structure Revealed

The map $W \mapsto L$ is:
$$\ell_2 = \rho \circ G(w_2)$$
$$\ell_1 = \begin{cases}
G(w_1) & w_2 = 0 \\
\rho \circ G(w_1) & w_2 \in \{1, 2\} \\
G(w_1) + 3 & w_2 = 3
\end{cases}$$

**This is piecewise affine!**

---

## 4. Main Finding: Piecewise Affine Structure

### 4.1 Theorem (Piecewise Affine Lifted Gray Code)

The lifted Gray code $\tilde{G}: (V_n)^m \to (V_n)^m$ is **not globally linear**, but it is **piecewise affine**.

The pieces are determined by the **pivot pattern**: which digits $w_i$ have non-identity $\mu(w_i)$.

### 4.2 Factorization Within Each Piece

For fixed pivot pattern $\sigma$:
$$\tilde{G}|_\sigma = \mathcal{A}_\sigma \circ (I_m \otimes G)$$

where:
- $I_m \otimes G$ applies $G$ componentwise (this is linear)
- $\mathcal{A}_\sigma$ is a fixed affine map (rotation + translation) that depends on $\sigma$

### 4.3 Why Not Globally Linear?

The nonlinearity arises because:
1. The rotation amount $\delta_k = \sum_{i<k} (d(w_i) + 1)$ depends on $w_1, \ldots, w_{k-1}$
2. The translation $e_k = \sum_{i<k} \rho^{-\delta_{i-1}}(e(w_i))$ has nested state dependence
3. Both $d(w)$ and $e(w)$ are nonlinear functions of $w$

---

## 5. Pivot Digits and Sparse Scans

### 5.1 Definition: Pivot Digit

A digit $w \in \{0, \ldots, 2^n - 1\}$ is a **pivot** if $\mu(w) \neq (0, 0)$.

### 5.2 Identity Conditions

$\mu(w) = \text{identity}$ requires both:
1. $e(w) = 0$, i.e., $G(2\lfloor(w-1)/2\rfloor) = 0$, i.e., $w \in \{1, 2\}$
2. $d(w) + 1 \equiv 0 \pmod n$

For $n = 2$: Identity digits are $\{1, 2\}$. Pivot digits are $\{0, 3\}$.

For general $n$: The identity set shrinks as $n$ grows (condition 2 becomes more restrictive).

### 5.3 Sparse Scan Structure

Since non-pivot digits contribute the identity, the scan can be "compressed":

$$S_k = \prod_{\substack{i \leq k \\ w_i \text{ is pivot}}} \mu(w_i)$$

This suggests an algorithm that:
1. Identifies pivot positions
2. Performs scan only over pivots
3. Propagates state to non-pivot positions

---

## 6. Tensor Product Interpretation

### 6.1 The Full Bit Matrix

View a point $p \in P$ as an $n \times m$ bit matrix:
$$B_{j,s} = \text{bit}_s(p_j)$$

View Hilbert index $h$ as an $m$-tuple of $n$-bit digits.

### 6.2 Decoding as Twisted Tensor Product

If the state were constant (no twisting), decoding would be:
$$L = (I_m \otimes G)(W)$$

The actual decoding is:
$$L = \mathcal{T}(W) \cdot (I_m \otimes G)(W)$$

where $\mathcal{T}$ is the "twisting" operator that applies state-dependent rotations and translations.

The twist depends on the scan of $\mu(W)$, creating the nonlinearity.

### 6.3 Twisted Semidirect Structure?

The group $\mathcal{H} = V_n \rtimes \mathbb{Z}_n$ acts on each level.

Conjecture: The full transformation might be expressible as an action of a **lifted group** $\mathcal{H}^m$ on $(V_n)^m$, where the action has a specific triangular/scan structure.

---

## 7. Comparison: Gray Code vs Lifted Gray Code

| Property | Standard $G$ | Lifted $\tilde{G}$ |
|----------|--------------|-------------------|
| Domain | $V_n$ | $(V_n)^m$ |
| Linearity | Linear | Piecewise affine |
| Pieces | 1 | Up to $(2^n - \text{identity count})^m$ |
| Structure | Bidiagonal matrix | Triangular system with state-dependent coefficients |
| Inverse | Upper triangular | Inverse scan + inverse transforms |

---

## 8. Implications for Parallelization

### 8.1 Decoding

The piecewise structure doesn't break parallelism for decoding because:
- The scan can be parallelized (associative operation)
- Once states are known, level transforms are embarrassingly parallel

### 8.2 Encoding: Parallel via Function Composition

At first glance, encoding seems inherently sequential due to the triangular dependency:
$$S_{i+1} = S_i \cdot \mu(W_i), \quad \text{where } W_i = \Phi_{S_i}(L_i)$$

Since $W_i$ depends on $S_i$, and $S_{i+1}$ depends on $W_i$, the chain appears unbreakable.

**However**, there is a powerful technique: **Parallel Prefix on Function Tables**.

### 8.3 The Transition Function Monoid

For each level label $L \in V_n$, define the **transition function**:
$$f_L: \mathcal{H} \to \mathcal{H}, \quad f_L(S) = S \cdot \mu(\Phi_S(L))$$

Key insight: **Function composition is associative.** The set of functions $\mathcal{H} \to \mathcal{H}$ forms a monoid under composition.

### 8.4 Parallel Encoding Algorithm

```
parallel_encode(p):
    # Step 1: Extract level labels (parallel, O(1) depth)
    L = [ℓ_m, ℓ_{m-1}, ..., ℓ_1]  # from coordinates

    # Step 2: Build transition function tables (parallel, O(1) depth)
    for i in 1..m parallel:
        f[i] = build_table(L[i])  # O(|H|) work per level

    # Step 3: Parallel prefix on function composition (O(log m) depth)
    F = parallel_scan(∘, identity, f)
    # F[k] = f_k ∘ f_{k-1} ∘ ... ∘ f_1

    # Step 4: Evaluate to get all states (parallel, O(1) depth)
    for k in 1..m parallel:
        S[k] = F[k-1](S_initial)

    # Step 5: Compute digits (parallel, O(1) depth)
    for k in 1..m parallel:
        W[k] = Φ_{S[k]}(L[k])

    return pack(W)
```

### 8.5 Complexity Comparison

| Resource | Sequential | Parallel (function tables) |
|----------|------------|---------------------------|
| Depth    | $O(m)$     | $O(\log m)$               |
| Work     | $O(m)$     | $O(m \cdot n \cdot 2^n)$  |
| Space    | $O(1)$     | $O(m \cdot n \cdot 2^n)$  |

### 8.6 Practical Viability

The function table size is $|\mathcal{H}| = n \cdot 2^n$:

| $n$ | $|\mathcal{H}|$ | Practical? |
|-----|-----------------|------------|
| 2   | 8               | ✓ Trivial  |
| 3   | 24              | ✓ Easy     |
| 4   | 64              | ✓ Feasible |
| 5   | 160             | ✓ Feasible |
| 6   | 384             | ✓ Feasible |
| 7   | 896             | Borderline |
| 8   | 2048            | Large but possible |

For typical Hilbert curve applications ($n \leq 6$), **both encoding and decoding are parallelizable**.

### 8.7 Why This Works: The Algebraic View

The sequential encoding is a **fold** over a monoid:
$$S_{\text{final}} = (f_{L_m} \circ f_{L_{m-1}} \circ \cdots \circ f_{L_1})(S_{\text{initial}})$$

Any fold over a monoid can be parallelized via scan, because the monoid operation (here, function composition) is associative.

This insight only emerges when viewing the problem algebraically—as a group action composed with a monoid fold—rather than as imperative state updates.

---

## 9. Open Questions

### 9.1 Closed-Form Piece Count

For dimension $n$, how many digits $w \in \{0, \ldots, 2^n - 1\}$ give $\mu(w) = \text{identity}$?

Conjecture: For $n \geq 2$, exactly 2 digits (namely 1 and 2) give $e(w) = 0$, but condition on $d(w)$ further restricts which are identity.

### 9.2 Alternative Formulations

Is there a different choice of generator $\mu'$ that makes more values identity? This would:
- Reduce the number of piecewise regions
- Simplify the lifted Gray code
- Still satisfy the gluing conditions for Hilbert curve continuity

### 9.3 Linear Approximation

Even though $\tilde{G}$ isn't linear, is there a "best linear approximation" that captures most of its structure? What's the "error" of treating it as linear?

### 9.4 Connection to Automata

The piecewise structure resembles a finite-state transducer:
- States are elements of $\mathcal{H}$
- Input is digit sequence
- Output is transformed digit sequence
- Transitions are given by $\mu$

Can we use automata theory to analyze the lifted Gray code?

---

## 10. Summary

The "lifted Gray code" $\tilde{G}: (V_n)^m \to (V_n)^m$ exists but is **not globally linear**.

Its structure is:
1. **Piecewise affine**: Partitioned by pivot patterns
2. **Within each piece**: $(I_m \otimes G)$ followed by a fixed affine twist
3. **Triangular dependence**: Level $k$ depends on all digits $w_1, \ldots, w_{k-1}$
4. **Sparse scan**: Only pivot digits change state

**Key parallelization results:**
- **Decoding**: $O(\log m)$ depth via parallel scan on the group $\mathcal{H}$
- **Encoding**: $O(\log m)$ depth via parallel scan on the **function monoid** $(\mathcal{H} \to \mathcal{H}, \circ)$

The encoding parallelization is the deeper result: it lifts from values to functions, exploiting that function composition is associative even when the underlying state evolution is nonlinear.

**For practical dimensions** ($n \leq 6$), both encoding and decoding achieve logarithmic depth with polynomial work overhead. The Hilbert curve's "inherently sequential" reputation is a myth—the algebraic structure unlocks parallelism.
