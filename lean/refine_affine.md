# Hilbert Curves via Affine Maps on an Axis‑Labeled Bit Space (Equal Sides)

This is a rewrite of `refine_hilbert.md`, aiming for a clearer “what is the state?” story:

> The Hilbert loop is a *scan (prefix composition)* of **affine maps** acting on an **axis‑labeled** vector space over GF(2).

The semidirect product from `refine_hilbert.md` is still there, but we keep it implicit: we work directly with *functions* and *composition* of affine maps rather than with an abstract group presentation.

This document treats the **hypercube** case (equal side lengths): all axes have the same precision.
At the end there is a short note on what changes in the anisotropic/activation setting.

---

## 0. Problem statement (equal sides)

Fix:

- Dimension: \(n \ge 1\)
- Precision per axis: \(m \ge 1\)
- Lattice (grid points):  
  \[
  P = \{0,1,\dots,2^m-1\}^n
  \]
- Index set:
  \[
  \{0,1,\dots,2^{mn}-1\}
  \]

We want a bijection
\[
H : \{0,\dots,2^{mn}-1\} \to P
\]
such that **lattice continuity** holds:
\[
\|H(h+1)-H(h)\|_1 = 1\quad\text{for all }0 \le h < 2^{mn}-1.
\]

The usual “Hilbert curve algorithm” is a loop that maintains an orientation state \((e,d)\) and reads/writes one \(n\)-bit “digit” per level. We will restate that loop as:

1. a **scan** of affine maps (to get all states), plus
2. embarrassingly parallel per-level computations.

---

## 1. Axis‑labeled GF(2) vectors

### 1.1 Axis labels

Let the set of axis labels be
\[
A := \{0,1,\dots,n-1\}.
\]

In the equal-sides case, this set is constant at every level.

### 1.2 The vector space \(V(A)=\mathrm{GF}(2)^A\)

Define
\[
V(A) := \{\,v : A \to \mathrm{GF}(2)\,\}.
\]
Concretely, we identify \(\mathrm{GF}(2)=\{0,1\}\) and write addition as XOR.

- Addition: \((u+v)(a)=u(a)\oplus v(a)\)
- Zero vector: \(0(a)=0\)
- Every vector is its own inverse: \(v+v=0\)

### 1.3 Standard basis and adjacency

For each axis label \(a\in A\), define the standard basis vector \(\mathbf{e}_a\in V(A)\) by:
\[
\mathbf{e}_a(a)=1,\quad \mathbf{e}_a(a')=0 \text{ for } a'\ne a.
\]

Two vectors \(u,v\in V(A)\) are **adjacent hypercube corners** iff
\[
u+v=\mathbf{e}_a \text{ for some } a\in A.
\]

This “one-hot XOR” characterization is the main invariant we keep using.

---

## 2. Linear maps: permutations of axes

### 2.1 Permutations act on \(V(A)\)

Any permutation \(\sigma\in\mathrm{Sym}(A)\) induces a linear automorphism of \(V(A)\) by relabeling coordinates:
\[
(\sigma\cdot v)(a) := v(\sigma^{-1}(a)).
 \]

Key facts:

- \(\sigma\cdot(\,u+v\,)=\sigma\cdot u + \sigma\cdot v\) (linearity)
- Permutations preserve adjacency:
  if \(u+v=\mathbf{e}_a\) then \((\sigma\cdot u)+(\sigma\cdot v)=\mathbf{e}_{\sigma(a)}\).

### 2.2 The cyclic rotation \(\rho\)

Fix the standard cyclic permutation \(\rho\in\mathrm{Sym}(A)\) by
\[
\rho(a) := (a+1)\bmod n.
\]

Then \(\rho^r\) is “rotation by \(r\)” (as a permutation of axis labels).

You can think of \(\rho\) as changing the *frame* that says “which axis is in position 0, 1, …”.
In the equal-sides setting, this is a symmetry; in the anisotropic setting, this becomes “rotation of the ordered active axis list”.

---

## 3. Affine maps on \(V(A)\)

### 3.1 Definition

An **affine map** on \(V(A)\) is a function of the form
\[
f(v)=\sigma\cdot v + t
\]
where \(\sigma\in\mathrm{Sym}(A)\) and \(t\in V(A)\).

Think of:

- \(\sigma\) = “rotation / axis relabeling” (linear part)
- \(t\) = “entry mask / translation” (affine part)

### 3.2 Composition rule

If \(f_1(v)=\sigma_1\cdot v + t_1\) and \(f_2(v)=\sigma_2\cdot v + t_2\), then
\[
(f_1\circ f_2)(v) = (\sigma_1\sigma_2)\cdot v + \bigl(t_1 + \sigma_1\cdot t_2\bigr).
\]

This is the algebraic heart of the Hilbert “state update”: the new translation \(t_2\) gets rotated by the current frame \(\sigma_1\).

### 3.3 Affine maps preserve hypercube edges

If \(u+v=\mathbf{e}_a\), then for any affine map \(f(v)=\sigma\cdot v + t\),
\[
f(u)+f(v) = (\sigma\cdot u+t)+(\sigma\cdot v+t) = \sigma\cdot(u+v) = \mathbf{e}_{\sigma(a)}.
\]

So affine maps (with permutation linear part) preserve “differ in exactly one bit”.

This is the clean conceptual reason why the Hilbert orientation machinery does not destroy Gray-code adjacency.

---

## 4. Gray code as a linear map

### 4.1 Binary ↔ axis‑labeled vectors

For this section only, we identify \(V(A)\) with \(n\)-bit words by the axis order \(0,1,\dots,n-1\).
(Axis labels are still present; we’re just choosing a coordinate system for writing formulas.)

### 4.2 The Gray map \(G : V(A)\to V(A)\)

Define \(G\) by:
\[
(G(v))_j =
\begin{cases}
v_j + v_{j+1} & j<n-1 \\
v_{n-1} & j=n-1.
\end{cases}
\]

This is the usual “\(g=b\oplus(b\gg 1)\)” Gray code in linear-algebra form.
It is a linear automorphism of \(V(A)\); its inverse is the “suffix XOR”:
\[
(G^{-1}(g))_j = \sum_{k=j}^{n-1} g_k \pmod 2.
\]

### 4.3 The Gray sequence is a hypercube Hamiltonian path

Let \(b(i)\in V(A)\) be the \(n\)-bit vector of the integer \(i\in\{0,\dots,2^n-1\}\) (least significant bit = axis \(0\)).

Define \(\mathrm{tsb}(i)\) (“trailing set bits”) to be the number of trailing 1-bits of \(i\), i.e. the largest \(t\) such that
\[
2^t \mid (i+1).
\]
(Equivalently: \(\mathrm{tsb}(i)=\mathrm{ctz}(i+1)\), the number of trailing 0-bits of \(i+1\).)

Then consecutive Gray outputs differ in exactly one bit:
\[
G(b(i))+G(b(i+1))=\mathbf{e}_{\mathrm{tsb}(i)}.
\]

We will use only the consequence: **Gray code gives an adjacent walk on the hypercube.**

---

## 5. The Hilbert orientation state as an affine map

Hamilton’s algorithm maintains two pieces of state:

- an “entry mask” \(e\in V(A)\)
- a direction index \(d\in\mathbb{Z}_n\)

In practice, \(d\) only ever appears as \(d+1\) inside a rotation. To make formulas cleaner, we define:

> **Rotation parameter:** \(\delta := d+1 \in \mathbb{Z}_n\).

### 5.1 The map we actually apply: “unrotate then XOR”

Define the affine map \(S_{e,\delta} : V(A)\to V(A)\) by
\[
S_{e,\delta}(x) := \rho^{-\delta}\cdot x + e.
\]

Interpretation:

- “unrotate by \(\delta\)” (apply \(\rho^{-\delta}\))
- then translate by the entry mask \(e\)

This is exactly the “rotate-left by \(d+1\), then XOR by \(e\)” inverse \(T^{-1}\) used in most decode formulations.

### 5.2 Inverse map (“XOR then rotate”)

The inverse is
\[
S_{e,\delta}^{-1}(y) = \rho^{\delta}\cdot (y+e).
\]

Interpretation:

- translate by \(e\) (XOR)
- then rotate by \(\delta\)

This is the forward \(T\)-transform used when encoding (extracting a digit from a plane label).

### 5.3 Per-level bijection: digit \(\leftrightarrow\) bit-plane label

At each level we relate:

- a **digit** \(w\in V(A)\) (the child index in binary),
- a **Gray vertex** \(g:=G(w)\in V(A)\),
- a **label** \(\ell\in V(A)\) which is the bit-plane we write into coordinates.

The per-level relation is:
\[
\ell = S_{e,\delta}(G(w)),
\qquad
w = G^{-1}(S_{e,\delta}^{-1}(\ell)).
\]

This is a bijection because \(G\) and \(S_{e,\delta}\) are bijections.

---

## 6. Child-relative transforms \(\mu(w)\) and “state update = composition”

The Hilbert curve’s geometry is encoded in two child functions (Hamilton Theorems 2.9 and 2.10):

- \(e(w)\in V(A)\): the child entry corner in the **standard orientation**
- \(d(w)\in\mathbb{Z}_n\): the child “intra-direction” in the standard orientation

Again we package \(d(w)\) as:
\[
\delta(w) := d(w)+1\in\mathbb{Z}_n.
\]

### 6.1 Closed forms for \(e(w)\) and \(d(w)\) (Hamilton)

For implementation it is convenient to treat a digit as an integer \(w\in\{0,\dots,2^n-1\}\) and convert it to a vector via \(b(w)\in V(A)\) (as in §4.3).

Hamilton’s definitions can be written:

- Entry corner:
  \[
  e(0)=0,\qquad e(w)=G\!\left(b\!\left(2\left\lfloor\frac{w-1}{2}\right\rfloor\right)\right)\ \text{for }w>0.
  \]
  (Equivalently: \(e(w)=G(b((w-1)\ \&\ \sim 1))\) for \(w>0\): clear the low bit of \(w-1\), then Gray.)
- Direction:
  \[
  d(0)=0,\qquad
  d(w)=
  \begin{cases}
  \mathrm{tsb}(w-1)\bmod n & w>0\ \text{even}\\
  \mathrm{tsb}(w)\bmod n & w\ \text{odd.}
  \end{cases}
  \]

These formulas are exactly what the equal-sides Hilbert “child orientation tables” compute; all other geometry is just “compose these relative moves”.

### 6.2 Define the child-relative affine map

Define:
\[
\mu(w) := S_{e(w),\,\delta(w)}.
\]

So \(\mu(w)\) is itself an affine map \(V(A)\to V(A)\).

### 6.3 State update by composition

Let the current state be the affine map \(S_{e,\delta}\).
After descending into child \(w\), the next state is:
\[
S_{e',\delta'} = S_{e,\delta}\circ \mu(w).
\]

Using the affine composition rule:

- rotation update:
  \[
  \delta' = \delta + \delta(w)\pmod n
  \]
- entry-mask update:
  \[
  e' = e + \rho^{-\delta}\cdot e(w)
  \]

This is the clean algebraic content of the imperative state update rule.

> If you prefer Hamilton’s \(d\) rather than \(\delta\), this is the same as:
> \(d' = d + d(w) + 1\) and \(e' = e + \rho^{-(d+1)}\cdot e(w)\).

### 6.4 Why this viewpoint is simpler

The loop invariant is simply:

> “The current orientation is represented by the affine map \(S_{e,\delta}\).”

Then every update is just composition by another affine map \(\mu(w)\), and associativity becomes automatic.

---

## 7. End-to-end decode (index → point)

### 7.1 Digits (“base \(2^n\)”)

Write the index \(h\) in base \(2^n\):
\[
h = \sum_{i=0}^{m-1} w_i \cdot (2^n)^{m-1-i}
\]
where each digit \(w_i\in\{0,\dots,2^n-1\}\).
We freely identify such digits with their \(n\)-bit vectors \(b(w_i)\in V(A)\).

### 7.2 Decode algorithm in affine form

We treat the Hilbert point \(p\in P\) as an \(m\times n\) bit-matrix in **MSB-first** plane order:

- row \(i\) = bit-plane with bit position \(s=m-1-i\) (so \(i=0\) is the MSB plane \(s=m-1\)),
- column \(a\in A\) = axis \(a\).

Concretely, if \(\ell_i(a)\in\{0,1\}\) is the bit in row \(i\), column \(a\), then
\[
p_a = \sum_{i=0}^{m-1} \ell_i(a)\,2^{m-1-i}.
\]

Algorithm:

1. Extract digits \(W=[w_0,\dots,w_{m-1}]\).
2. Compute the relative transforms \(M_i := \mu(w_i)\).
3. Compute the sequence of states by scan:
   \[
   S_0 := S_{0,1},
   \qquad
   S_{i+1} := S_i \circ M_i.
   \]
4. For each level \(i\), compute the plane label:
   \[
   \ell_i := S_i(G(w_i)) \in V(A).
   \]
5. Scatter \(\ell_i\) into the output point bits at plane \(m-1-i\).

Pseudocode (mathematical):

```text
decode(h):
  W := digits_base_2^n(h)          # length m, MSB-first
  M[i] := μ(W[i])                  # affine maps
  S := scanl(compose, S_{0,1}, M)  # states S[0..m]
  for i in 0..m-1:
    ℓ[i] := S[i]( G(W[i]) )
  p := scatter_planes(ℓ)           # write ℓ[i] into bit-plane (m-1-i)
  return p
```

### 7.3 Complexity (decode)

Let “unit cost” mean \(O(n)\) bit operations per level for \(G\), \(\rho\), XOR, and scatter.

- Total work: \(O(mn)\)
- Parallel depth:
  - scan is \(O(\log m)\) depth,
  - the per-level \(G(\cdot)\), application of \(S_i\), and scatter are all parallel over \(i\),
  so overall decode depth can be \(O(\log m)\) with \(O(mn)\) work.

This matches the key point in `refine_hilbert.md`, but now the scan is literally “compose affine maps”.

---

## 8. End-to-end encode (point → index)

Encoding is the reverse direction: we start from bit-planes \(\ell_i\) and must recover digits \(w_i\).
The crucial asymmetry is that the state depends on the digits we are recovering.

### 8.1 Encode algorithm

1. Gather each plane label \(\ell_i \in V(A)\) from the point’s bits.
2. Initialize state \(S := S_{0,1}\).
3. For each level \(i\):
   - compute \(g_i := S^{-1}(\ell_i)\),
   - compute \(w_i := G^{-1}(g_i)\),
   - update state \(S := S \circ \mu(w_i)\).
4. Pack the digits into \(h\).

Pseudocode:

```text
encode(p):
  ℓ := gather_planes(p)            # ℓ[0..m-1] in V(A), MSB-first planes
  S := S_{0,1}
  for i in 0..m-1:
    g := S^{-1}(ℓ[i])
    W[i] := G^{-1}(g)
    S := S ∘ μ(W[i])
  h := pack_base_2^n(W)
  return h
```

### 8.2 Complexity (encode)

- Work: \(O(mn)\)
- Depth: \(O(m)\) (inherently sequential in general), because \(W[i]\) depends on state \(S\), and \(S\) depends on previous digits.

This is the same “triangular dependency” observation as in `refine_hilbert.md`, now phrased as “can’t parallelize the scan because the scan inputs \(\mu(w_i)\) are unknown until you compute \(w_i\)”.

---

## 9. Proof story (equal sides)

This section explains why the above definitions prove the standard correctness statements.

### 9.1 Encode/decode are inverses

Key facts:

1. \(G\) is a bijection on \(V(A)\).
2. Each \(S_{e,\delta}\) is a bijection, with explicit inverse.
3. The state update is composition in an associative monoid (affine maps under composition).

Then:

- In **decode**, states \(S_i\) are computed from the digit sequence by a scan, and each \(\ell_i\) is computed by \(\ell_i = S_i(G(w_i))\).
- In **encode**, given the same \(\ell_i\), we recover \(g_i = S_i^{-1}(\ell_i)\) and thus \(w_i = G^{-1}(g_i)\).

Inductively, encoding reconstructs the same digits that decoding started from, and the state updates match because both are just composing the same \(\mu(w_i)\) in the same order.

That proves:
\[
\mathrm{encode}(\mathrm{decode}(h))=h,\quad
\mathrm{decode}(\mathrm{encode}(p))=p.
\]

### 9.2 Why lattice continuity reduces to “a seam step”

The Hilbert path is built by:

- at each level, choosing a child index \(w_i\),
- and within each child, recursing.

Incrementing \(h\to h+1\) is exactly “add 1 in base \(2^n\)” on the digit sequence \((w_0,\dots,w_{m-1})\):

- low digits overflow (wrap from all-ones to zero),
- one pivot digit increments by 1,
- higher digits stay fixed.

So the global step decomposes into:

1. many “within-child” steps (handled inductively), and
2. exactly one “seam” step between two consecutive children at the pivot level.

### 9.3 The seam step is a unit \(L^1\) step

At the pivot level the two child indices are consecutive, \(w\to w+1\).

1. **Gray adjacency:** \(G(w)\) and \(G(w+1)\) differ in one bit:
   \[
   G(w)+G(w+1)=\mathbf{e}_a \text{ for some } a.
   \]
2. **Affine preservation:** applying \(S_{e,\delta}\) preserves one-bit difference:
   \[
   S_{e,\delta}(G(w)) + S_{e,\delta}(G(w+1)) = \mathbf{e}_{\rho^{-\delta}(a)}.
   \]
   So the two *plane labels* differ in exactly one axis bit at that plane.
3. **Geometric meaning:** changing exactly one bit at plane \(s\) changes exactly one coordinate by \(2^s\) at the dyadic scale; when you look at the *boundary corners* where the recursion exits one child and enters the next, that change becomes a \(\pm 1\) step in the integer lattice at the finest scale (this is the “corner of low half vs corner of high half” argument).

That yields the unit \(L^1\) seam step, and the induction gives unit steps everywhere.

This is the same proof skeleton as `discrete_proof.md` (Lemmas 5.1–5.4), just stated in the language where “preserves oneHot XOR” is a one-line affine-map fact.

---

## 10. What changes in the anisotropic (activation) setting? (brief)

The GF(2)/affine-map story still works, but the *space you act on changes with level*.

At level \(s\), the active axes are a subset \(A_s\subseteq A\), so you should work in
\[
V(A_s)=\mathrm{GF}(2)^{A_s}.
\]

Two additional pieces appear:

1. **The permutation part is a permutation of \(A_s\)** (rotation of the *ordered active list*), not a permutation of all axes.
2. **Embedding when \(A_s\) grows:** when moving to a lower level with more active axes, you must transport state along the inclusion \(A_{s+1}\subseteq A_s\). This is exactly what the activation embedding rule enforces.

Conceptually:

- equal-sides: one fixed affine group acting on one fixed \(V(A)\),
- anisotropic: a compatible family of affine actions on \(V(A_s)\) with coherent embeddings.

That is why “axis labels” are the right abstraction: you preserve the *physical axis*, not the current position in a changing list.
