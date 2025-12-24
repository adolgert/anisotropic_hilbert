# Anisotropic Hilbert Curves via Affine Maps on Axis‑Labeled Bit Spaces

This document generalizes `refine_affine.md` from the **isotropic** (“equal sides”) Hilbert curve
to the **anisotropic / activation** setting (unequal per-axis precisions), in the style of
`discrete_proof.md` and the Lean implementation in `AnisoHilbert/Loops.lean`.

> The one-sentence punchline is still:
> the encoder/decoder is “Gray code + affine state”,
> except now the state lives on a **varying active-axis list** and we add a coherent **embedding**
> step when new axes activate.

We keep the axis‑labeled viewpoint throughout: the “direction” is best treated as a **physical axis**
label, not just an index in a changing list.

---

## 0. Problem statement (anisotropic dyadic box)

Fix:

- Dimension \(n \ge 1\), global axis labels \(J := \{0,1,\dots,n-1\}\).
- Per-axis precisions \(m = (m_j)_{j\in J}\) with \(m_j \in \mathbb{N}\).

Define the grid:
\[
P(m) := \prod_{j\in J}\{0,1,\dots,2^{m_j}-1\}.
\]
Let total precision \(M := \sum_{j\in J} m_j\). The anisotropic Hilbert curve is a bijection
\[
H_m : \{0,\dots,2^M-1\} \to P(m)
\]
with **lattice continuity**
\[
\|H_m(h+1)-H_m(h)\|_1 = 1 \quad\text{for all } 0 \le h < 2^M-1.
\]

The “activation” phenomenon is that at high bit-planes, some axes have no bits available (their
precision is too small), so those axes are “inactive” until you reach low enough planes.

---

## 1. Levels and active axes

Let
\[
m_{\max} := \max_{j\in J} m_j.
\]
We process bit-planes **MSB-first** using the level parameter
\[
s \in \{m_{\max}, m_{\max}-1, \dots, 1\},
\qquad i := s-1 \in \{m_{\max}-1, \dots, 0\}.
\]
(So \(i\) is the bit index within coordinates; \(s\) is its 1-based version.)

### 1.1 Active axis set and ordered active list

At level \(s\), axis \(j\) is **active** iff it has a bit at position \(i=s-1\), i.e.
\[
j \in A_s \quad \Longleftrightarrow \quad m_j \ge s.
\]

We need not only the set \(A_s\) but an **ordered list** of active axes, because the Hilbert
rotations and Gray code act on an ordered \(k\)-bit word.

Fix the priority order \(\pi\) on \(J\) (as in `discrete_proof.md`):
\[
j \prec_\pi j' \iff (m_j,j) < (m_{j'},j') \text{ lexicographically.}
\]
Define the ordered active-axis list:
\[
A_s = [a^{(s)}_0,\dots,a^{(s)}_{k_s-1}]
\]
as the axes satisfying \(m_j \ge s\), listed in increasing \(\pi\)-order. Let \(k_s := |A_s|\).

Monotonicity:
\[
A_{s+1} \subseteq A_s \quad (\text{as sets}), \qquad k_{s+1} \le k_s.
\]
Equivalently: as we go to *lower* bit-planes (smaller \(s\)), more axes can activate.

---

## 2. Axis‑labeled GF(2) vectors on \(A_s\)

At each level \(s\) we work in the vector space
\[
V(A_s) := \mathrm{GF}(2)^{A_s} = \{\,v : A_s \to \{0,1\}\,\}
\]
with addition as XOR.

Adjacency of two corners \(u,v \in V(A_s)\) means:
\[
u+v=\mathbf{e}_a \text{ for some } a\in A_s
\]
where \(\mathbf{e}_a\) is the “one-hot” vector at axis label \(a\).

This is the invariant that makes lattice continuity proofs work: “differ in one bit” is stable
under the operations we use (Gray code, rotations, XOR by entry masks).

---

## 3. Packing/unpacking a level bit-plane

Write a point \(p\in P(m)\) in bits. Let \(\mathrm{bit}(p_j,i)\in\{0,1\}\) be the \(i\)-th bit
of coordinate \(p_j\) (LSB = \(i=0\)).

At level \(s\) (bit index \(i=s-1\)) define the packed plane label \(\ell_s \in V(A_s)\) by:
\[
\ell_s(j) := \mathrm{bit}(p_j, s-1) \quad \text{for } j\in A_s.
\]

Concretely (matching `AnisoHilbert/Representation.lean`):

- `packPlane A_s p (s-1)` produces \(\ell_s\) as a \(k_s\)-bit word in the list order of \(A_s\).
- `writePlane A_s ℓ p (s-1)` writes those bits back into the point (touching only axes in \(A_s\)).

Axes not in \(A_s\) are simply absent at that level; conceptually, they are “filled with 0”.

---

## 4. Rotations on the ordered active list

Because \(A_s\) is an ordered list, we have a cyclic permutation “rotate the active positions”.
Define \(\rho_s \in \mathrm{Sym}(A_s)\) by
\[
\rho_s(a^{(s)}_t) := a^{(s)}_{(t+1)\bmod k_s}.
\]

As in `refine_affine.md`, permutations act linearly on \(V(A_s)\) by relabeling coordinates:
\[
(\sigma\cdot v)(a) := v(\sigma^{-1}(a)).
\]

Rotations preserve one-hot differences: if \(u+v=\mathbf{e}_a\) then
\((\rho_s^r\cdot u)+(\rho_s^r\cdot v)=\mathbf{e}_{\rho_s^r(a)}\).

---

## 5. Gray code at variable width \(k_s\)

Gray code is applied only to the active \(k_s\) bits at that level.
Define \(G_s : V(A_s)\to V(A_s)\) by the usual “\(g=b\oplus(b\gg 1)\)” formula in the list order of \(A_s\).
It is a linear automorphism with inverse \(G_s^{-1}\) (“suffix XOR”).

Key property: enumerating \(w\in V(A_s)\) in integer order and mapping through \(G_s\) yields a
Hamiltonian path of the \(k_s\)-cube (consecutive outputs differ in exactly one axis bit).

---

## 6. Orientation state as an affine map on \(V(A_s)\)

At each level \(s\), Hamilton’s per-level state consists of:

- entry mask \(e_s \in V(A_s)\),
- direction \(d_s \in \mathbb{Z}_{k_s}\) (an index modulo \(k_s\)).

In practice the rotation is always by \(d_s+1\), so set \(\delta_s := d_s+1\in\mathbb{Z}_{k_s}\).

Define the affine map
\[
S_{e_s,\delta_s}(x) := \rho_s^{-\delta_s}\cdot x + e_s.
\]
This is exactly “rotate-left by \(d_s+1\), then XOR by \(e_s\)”, i.e. the inverse \(T^{-1}\) used in decoding.

Its inverse is
\[
S_{e_s,\delta_s}^{-1}(y) = \rho_s^{\delta_s}\cdot (y+e_s),
\]
which is “XOR by \(e_s\), then rotate-right by \(d_s+1\)”, i.e. \(T\) used in encoding.

Intuition (same as isotropic, but now \(k_s\) changes):

- XOR by \(e_s\) re-centers the local cube so “entry corner = 0”.
- Rotation by \(d_s+1\) aligns the **canonical** Gray/Hilbert exit axis (the MSB position in the active list)
  with the cube’s **actual** exit direction.

---

## 7. Child geometry \(\mu_s(w)\) and state update

At level \(s\), the active dimension is \(k_s\). Hamilton’s child geometry is therefore computed
in a \(k_s\)-dimensional cube:

- entry corner \(e^{(k_s)}(w)\in V(A_s)\),
- intra-direction \(d^{(k_s)}(w)\in\mathbb{Z}_{k_s}\),
- \(\delta^{(k_s)}(w):=d^{(k_s)}(w)+1\).

Here \(\mathrm{tsb}(x)\) (“trailing set bits”) means: the number of consecutive 1-bits at the
least-significant end of \(x\)’s binary expansion (equivalently \(\mathrm{tsb}(x)=\mathrm{ctz}(x+1)\)).

Closed forms (Hamilton Theorems 2.9–2.10) depend only on \(k_s\) and the integer value of the digit \(w\):
\[
e^{(k)}(0)=0,\qquad e^{(k)}(w)=G\!\left(2\left\lfloor\frac{w-1}{2}\right\rfloor\right)\ (w>0),
\]
\[
d^{(k)}(0)=0,\qquad
d^{(k)}(w)=
\begin{cases}
\mathrm{tsb}(w-1)\bmod k & w>0\ \text{even}\\
\mathrm{tsb}(w)\bmod k & w\ \text{odd.}
\end{cases}
\]

Define the child-relative affine map:
\[
\mu_s(w) := S_{e^{(k_s)}(w),\,\delta^{(k_s)}(w)} : V(A_s)\to V(A_s).
\]

Then (within the *same* active list \(A_s\)) the state update is exactly composition:
\[
S' = S \circ \mu_s(w).
\]
Unpacking that gives:
\[
\delta'_s = \delta_s + \delta^{(k_s)}(w)\pmod{k_s},
\qquad
e'_s = e_s + \rho_s^{-\delta_s}\cdot e^{(k_s)}(w).
\]

Equivalently, if you track the *axis label* \(\mathrm{dirAxis}_s \in A_s\) rather than the raw index \(d_s\),
the direction update is “rotate the physical axis within the current active list”:
\[
\mathrm{dirAxis}'_s = \rho_s^{\delta^{(k_s)}(w)}(\mathrm{dirAxis}_s).
\]

---

## 8. Activation embedding (the anisotropic step)

Between consecutive levels, the active list can grow:
\[
A_s \subseteq A_{s-1}.
\]
We must transport the state from \(V(A_s)\) to \(V(A_{s-1})\).

### 8.1 Embedding vectors: “copy shared axes, zero newly-activated axes”

Define the linear embedding (matching `Embed.embedBV`):
\[
\iota_{s\to s-1} : V(A_s)\to V(A_{s-1})
\]
by:
- if axis \(j\in A_s\), then \((\iota x)(j)=x(j)\),
- if \(j\in A_{s-1}\setminus A_s\) (newly activated), then \((\iota x)(j)=0\).

### 8.2 Embedding direction: preserve the *axis label*

The important subtlety is direction. Since the list order changes when axes activate, the raw index
\(d_s\in\mathbb{Z}_{k_s}\) is not stable across levels.

Instead, treat direction as a **physical axis label**
\[
\mathrm{dirAxis}_s \in A_s.
\]
When embedding to level \(s-1\):

- keep \(\mathrm{dirAxis}_{s-1} := \mathrm{dirAxis}_s\) (the axis itself does not change),
- recompute \(d_{s-1}\) as the position of that axis in the new list \(A_{s-1}\).

This is exactly why the Lean `State` stores both `dirAxis` and `dPos` and proves they match.

---

## 9. End-to-end decode (index → point) in the activation setting

The natural “mixed-radix” view is:

- at each level \(s\) you choose a digit \(w_s \in V(A_s)\) (a \(k_s\)-bit word),
- total index length is \(\sum_s k_s = \sum_j m_j = M\).

In Lean (`AnisoHilbert/Loops.lean`) the index is represented as a list of variable-width digits
\(\langle k_s,w_s\rangle\) rather than a single \(M\)-bit integer; you can always pack/unpack those
digits into an integer by concatenating bits MSB-first.

### 9.1 Decode loop

Initialize:

- \(s_0 := m_{\max}\),
- \(A_{s_0} := A_{m_{\max}}\),
- \(e := 0\in V(A_{s_0})\),
- \(d := 0\in \mathbb{Z}_{k_{s_0}}\) (the first axis in the list is the initial direction),
- \(p := 0\in P(m)\).

Then for \(s = m_{\max}, m_{\max}-1, \dots, 1\):

1. Read digit \(w_s \in V(A_s)\).
2. Compute the packed plane label:
   \[
   \ell_s := S_{e,\delta}(G_s(w_s)) \quad (\text{i.e. } T^{-1}(e,d)(\mathrm{gc}(w_s))).
   \]
3. Write \(\ell_s\) into \(p\) at bit position \(i=s-1\) for axes in \(A_s\).
4. Update state within \(A_s\) using \(w_s\).
5. If \(s>1\), embed \((e,d)\) from \(A_s\) to \(A_{s-1}\) by “copy+zero” and direction reindexing.

This matches the structure of `decodeFromLevel` in `AnisoHilbert/Loops.lean`.

### 9.2 Optional: “decode is still a scan”

In the isotropic case, decode states can be computed by a scan of group elements \(\mu(w_i)\).
In the anisotropic case, the width changes, but you can still view decode as a scan of
**state-transformer functions**:
\[
F_s : \mathrm{State}(A_s) \to \mathrm{State}(A_{s-1}),\qquad
F_s(st) := \mathrm{embed}\bigl(\mathrm{stateUpdate}(st,w_s)\bigr).
\]
Then the sequence of states is a prefix-composition of the \(F_s\).
This is conceptually useful (and still parallelizable in principle), but a straightforward
implementation is usually sequential.

---

## 10. End-to-end encode (point → index) in the activation setting

Encoding is the reverse direction. For \(s=m_{\max},\dots,1\):

1. Pack the plane label \(\ell_s \in V(A_s)\) from the point bits at position \(i=s-1\).
2. Compute
   \[
   w_s := G_s^{-1}(S_{e,\delta}^{-1}(\ell_s)) \quad (\text{i.e. } \mathrm{gc}^{-1}(T(e,d)(\ell_s))).
   \]
3. Emit digit \(w_s\).
4. Update state within \(A_s\) using \(w_s\).
5. If \(s>1\), embed the state to \(A_{s-1}\).

This matches `encodeFromLevel` in `AnisoHilbert/Loops.lean`.

---

## 11. Complexity and caching notes

Let \(M=\sum_j m_j\) and note \(\sum_{s=1}^{m_{\max}} k_s = M\).

At level \(s\), all per-level operations are \(O(k_s)\) bit operations:
Gray, rotations, XOR, and packing/writing \(k_s\) bits.

So both encode and decode do:
\[
O\!\left(\sum_s k_s\right) = O(M)
\]
work. Depth is sequential in \(m_{\max}\) in the straightforward implementation.

Practical cache-friendly choices:

- Precompute all lists \(A_s\) and their lengths \(k_s\).
- Precompute, for each level \(s\), a lookup “axis \(\mapsto\) position in \(A_s\)” to make embedding
  and packing fast.
- Represent digits as variable-width chunks (as in the Lean code) until you actually need a packed integer.

---

## 12. Proof story (what the affine viewpoint buys you)

The proof skeleton from `refine_affine.md` still applies, with one extra compatibility fact.

1. **Per-level bijection:** \(w_s \leftrightarrow \ell_s\) is a bijection because \(G_s\) and \(S_{e,\delta}\) are bijections.
2. **State update = composition:** within each \(A_s\), the new state is obtained by composing with \(\mu_s(w_s)\).
3. **Embedding coherence:** embedding preserves the physical direction axis and sets newly activated entry bits to 0;
   this is exactly the rule that makes encode and decode agree across activation events.
4. **Adjacency preservation:** Gray code gives one-bit differences; affine maps preserve one-bit differences; embedding
   does not introduce differences on newly activated axes (they are 0 on both sides).

That is why the anisotropic continuity proof is still “induction + one seam step”:
the only genuinely new work is showing the activation embedding is consistent (and that’s where axis labels matter).
