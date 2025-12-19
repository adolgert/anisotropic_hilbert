### Goal and scope of the proof

Fix integers $n\ge 1$ and a dyadic box shape
$$
m=(m_0,\dots,m_{n-1})\in \mathbb{N}^n,\qquad
P(m)=\prod_{j=0}^{n-1}{0,1,\dots,2^{m_j}-1}.
$$
Let $M=\sum_j m_j$. The goal is to construct a bijection
$$
H_m:{0,1,\dots,2^M-1}\to P(m)
$$
such that the induced traversal $\bigl(H_m(h)\bigr)_{h=0}^{2^M-1}$ is **lattice-continuous**:
$$
|H_m(h+1)-H_m(h)|_1 = 1\quad\text{for all }0\le h<2^M-1.
$$
This is the discrete (“Hilbert lattice”) analogue of Hamilton’s observation that Hilbert lattice curves “always take steps of unit length.” 

What follows is a proof that the Python implementation you received (encode/decode with activation embedding) indeed defines such an $H_m$, and that `encode` and `decode` are exact inverses.

---

## 1. Preliminaries borrowed from Hamilton

### 1.1 Gray code

Let $gc:{0,\dots,2^k-1}\to{0,\dots,2^k-1}$ be the binary reflected Gray code, and $gc^{-1}$ its inverse (Hamilton Theorem 2.1 / 2.2, not repeated here). The key property is: consecutive Gray code values differ in exactly one bit, i.e. are neighboring cube vertices (Hamilton’s discussion around Gray codes and hypercube neighbors). This is the standard basis for Hilbert lattice adjacency.

### 1.2 The $T$-transform and its properties

For $k\ge 1$, a $k$-bit entry mask $e\in{0,\dots,2^k-1}$, and a direction index $d\in \mathbb{Z}*k$, Hamilton defines
$$
T*{(e,d)}(b) ;=; (b\oplus e);\copyright;(d+1),
$$
i.e. XOR by $e$ followed by cyclic right rotation of $k$ bits by $d+1$. 
Hamilton notes $T$ is bijective as a composition of bijections. 

Crucially, Hamilton also states (immediately after Lemma 2.11) that XOR + bit-rotation preserves the “differ in one bit” property, hence preserves Gray-adjacency. 

He gives an explicit inverse transform (Lemma 2.12). 
(Your code implements the equivalent “rotate-left then XOR” inverse, which is the same inversion logic.)

### 1.3 Hilbert cube entry/exit machinery

Hamilton defines the sequences $e(i)$ (“entry corner of the $i$-th subcube”) and $d(i)$ (“intra-subcube direction”), with the relationship (Equation $1$) encoding how consecutive subcubes glue along a shared face:
$$
e(i+1) = e(i)\oplus 2^{d(i)}\oplus 2^{g(i)}. \tag{H1}
$$


He provides closed forms for $d(i)$ (Theorem 2.9)  and $e(i)$ (Theorem 2.10). 

Finally, the Hilbert orientation state update rule used in indexing (Algorithm 2) is:
$$
e \leftarrow e \oplus \bigl(e(w);\text{left-rotated by }(d+1)\bigr),\qquad
d \leftarrow d+d(w)+1\pmod n.
$$

This is derived from composing transforms (Lemma 2.13). 

---

## 2. The anisotropic (“activation”) setting

Hamilton’s “unequal precision” observation is: if axis $j$ has precision $m_j$, then at bit-plane $i\ge m_j$ the bit is forced 0, and one can define an “active mask” $\alpha_j=1$ iff $m_j>i$. 

We recast that in the level parameter
$$
s=i+1\in{1,\dots,m_{\max}},\quad m_{\max}=\max_j m_j,
$$
so “axis $j$ is active at level $s$” means $m_j\ge s$.

### 2.1 Ordered active axis lists

Fix once and for all an axis priority order $\pi$ on ${0,\dots,n-1}$ defined by
$$
j\prec_\pi j' \iff (m_j,j) < (m_{j'},j')\text{ lexicographically}.
$$
(Shorter dimensions first; tie-break by axis index.)

For each level $s$, define the ordered active axis list
$$
A_s = [a^{(s)}*0,\dots,a^{(s)}*{k_s-1}]
\quad\text{where}\quad
{a^{(s)}_t}={j: m_j\ge s},
$$
listed in increasing $\pi$-order; $k_s=|A_s|$.

Then $A_{s+1}\subseteq A_s$ $monotone activation as (s\downarrow)$.

### 2.2 Packing and unpacking the level bit-plane

For a point $p\in P(m)$, define the $k_s$-bit packed word
$$
\ell_s(p)=\sum_{t=0}^{k_s-1} \mathrm{bit}\bigl(p_{a^{(s)}_t},,s-1\bigr);2^t.
$$
This is the level-$s$ “cube corner label” for the active axes at that level.

---

## 3. Construction of $H_m$ via the encode/decode algorithms

### 3.1 Definition of the index digits and state

We define a level-dependent Hilbert state $(e_s,d_s)$ where:

* $e_s\in {0,\dots,2^{k_s}-1}$,
* $d_s\in \mathbb{Z}_{k_s}$.

The index $h$ is represented in variable-width base $2^{k_s}$ “digits”
$$
h = (w_{m_{\max}};|,w_{m_{\max}-1};|,\cdots|,w_1),
\quad w_s\in{0,\dots,2^{k_s}-1}.
$$
So $h$ has exactly $\sum_s k_s = \sum_j m_j = M$ bits.

### 3.2 Encoding rule

At each level $s=m_{\max},m_{\max}-1,\dots,1$:

1. Compute $\ell_s(p)$.
2. Transform and Gray-decode:
   $$
   w_s = gc^{-1}!\left(T_{(e_s,d_s)}(\ell_s(p))\right).
   $$
3. Update $(e_s,d_s)$ using Hamilton’s cube rule (Algorithm 2) but in dimension $k_s$: 
   $$
   e \leftarrow e \oplus \bigl(e_{k_s}(w_s);\text{rotL}(d+1)\bigr),\qquad
   d \leftarrow d+d_{k_s}(w_s)+1 \pmod{k_s},
   $$
   where $e_{k_s}(\cdot)$ and $d_{k_s}(\cdot)$ are Hamilton’s sequences (Theorem 2.10 / 2.9).  
4. If $k_{s-1}>k_s$ (activation event), **embed** the state from $A_s$ to $A_{s-1}$ by:

   * copying bits of $e$ along shared axes,
   * setting newly activated axes’ bits of $e$ to 0,
   * reindexing $d$ so it still refers to the same physical axis (this is exactly the “treat $d$ as an axis label, not a raw index” fix).

This produces $h=\mathrm{encode}(p)$.

### 3.3 Decoding rule

At each level $s$ in the same order, read the digit $w_s$ from $h$, then:
$$
\ell_s = T_{(e_s,d_s)}^{-1}(gc(w_s)),
$$
and write $\mathrm{bit}(p_{a^{(s)}_t},s-1)=\mathrm{bit}(\ell_s,t)$, then update and embed the state exactly as in encoding.

This produces $p=\mathrm{decode}(h)$.

---

## 4. Proof that `encode` and `decode` are inverses (bijection)

### Lemma 4.1 $Per-level bijection between (\ell_s) and (w_s)$

For fixed $k\ge 1$, fixed state ((e,d)), the map
$$
\Phi_{(e,d)}:{0,\dots,2^k-1}\to{0,\dots,2^k-1},\quad
\Phi_{(e,d)}(\ell)=gc^{-1}(T_{(e,d)}(\ell))
$$
is a bijection, and its inverse is
$$
\Phi^{-1}*{(e,d)}(w)=T^{-1}*{(e,d)}(gc(w)).
$$

**Proof.** $T_{(e,d)}$ is bijective. 
$gc$ is bijective with inverse $gc^{-1}$.
Therefore $\Phi_{(e,d)}$ is a composition of bijections, hence bijective, and the stated inverse follows by reversing the steps (using the inverse transform given by Hamilton’s Lemma 2.12).  ∎

### Lemma 4.2 (State update consistency)

At each level $s$, both encoding and decoding update ((e,d)) by the same deterministic function of ((e,d)) and $w_s$, namely Hamilton’s Algorithm 2 update $with dimension (k_s)$. 

### Lemma 4.3 (Activation embedding consistency)

At any activation event $A_s\subset A_{s-1}$, both encoding and decoding apply the same embedding map: the same axes are newly activated, their entry bits are set to 0, and the direction axis is preserved by reindexing to the new axis list.

This step is deterministic and does not depend on $p$ or $h$ beyond the already-known state; it therefore commutes with “encode then decode” and “decode then encode.”

### Theorem 4.4 (Mutual inverses)

For every $m$ and every $p\in P(m)$,
$$
\mathrm{decode}(\mathrm{encode}(p,m),m)=p,
$$
and for every $h\in{0,\dots,2^M-1}$,
$$
\mathrm{encode}(\mathrm{decode}(h,m),m)=h.
$$

**Proof.** Consider one level $s$. Suppose the state at entry to level $s$ matches in both procedures. Encoding computes $w_s=\Phi_{(e,d)}(\ell_s(p))$. Decoding recovers $\ell_s$ from $w_s$ by $\Phi^{-1}*{(e,d)}$ (Lemma 4.1), hence writes exactly the same bit-plane bits back into the same coordinates. Then both apply the same state update (Lemma 4.2) and the same embedding when needed (Lemma 4.3). Inducting over $s=m*{\max}\downarrow 1$ proves both identities. ∎

As a corollary, $H_m(h)=\mathrm{decode}(h,m)$ is a bijection $ {0,\dots,2^M-1}\leftrightarrow P(m)$.

---

## 5. Proof of lattice continuity $|H_m(h+1)-H_m(h)|_1=1$

This is the core “Hilbert lattice continuity” statement.

### Lemma 5.1 (Oriented Gray order of children differs in one active bit)

Fix a level with $k$ active axes and fixed ((e,d)). Define the oriented Gray sequence
$$
u(i)=T^{-1}_{(e,d)}(gc(i)),\qquad i=0,\dots,2^k-1.
$$
Hamilton explicitly states this produces a Gray code sequence (hence successive values differ in one bit). 
(Conceptually: $T$ preserves adjacency, so transforming the standard Gray code yields another Gray code.) 

Therefore $u(i)\oplus u(i+1)=2^{g(i)}$ for some $g(i)\in{0,\dots,k-1}$.

### Lemma 5.2 (Hilbert child endpoints glue along that bit)

In Hamilton’s hypercube construction, if the $i$-th and $(i+1)$-st subcubes are neighbors along axis $g(i)$, then the exit corner $f(i)$ of subcube $i$ and the entry corner $e(i+1)$ of subcube $i+1$ satisfy:
$$
e(i+1)=f(i)\oplus 2^{g(i)}.
$$
This is exactly what Equation $1$ encodes when you rewrite $f(i)=e(i)\oplus 2^{d(i)}$: 
$$
e(i+1)=e(i)\oplus 2^{d(i)}\oplus 2^{g(i)} = f(i)\oplus 2^{g(i)}.
$$
So the exit of one child and entry of the next differ in one bit (hence are adjacent cube corners).

### Lemma 5.3 (Cube-corner adjacency implies unit lattice step after scaling)

Consider a dyadic interval of length $2^s$ along a single axis, split into two halves:

* low half: ${0,\dots,2^{s-1}-1}$,
* high half: ${2^{s-1},\dots,2^s-1}$.

The high endpoint of the low half is $2^{s-1}-1$, and the low endpoint of the high half is $2^{s-1}$; these differ by 1.

In $n$D, if two subboxes differ only by the choice of half along exactly one axis (and are identical along others), then a corner on the “high face” of the low-half box is a unit $L^1$ neighbor of the corresponding corner on the “low face” of the high-half box.

### Theorem 5.4 (Lattice continuity)

Let $H_m(h)=\mathrm{decode}(h,m)$. Then for all $0\le h<2^M-1$,
$$
|H_m(h+1)-H_m(h)|_1=1.
$$

**Proof (by hierarchical decomposition on the most significant changing digit).**

Write each index $h$ in its variable-width digit sequence $(w_{m_{\max}},\dots,w_1)$. When incrementing $h\to h+1$, there exists a smallest level $s^\star$ (closest to 1) such that:

* the digits for levels $1,2,\dots,s^\star-1$ overflow (wrap from max to 0),
* the digit $w_{s^\star}$ increases by 1 $in the (k_{s^\star})-bit digit$,
* digits above $s^\star$ remain unchanged.

Interpretation: the traversal moves from the last point of one level-$s^\star$ child subbox to the first point of the next level-$s^\star$ child subbox, while staying within the same coarser parent subbox.

Inside a fixed parent at level $s^\star$, the children are ordered by the oriented Gray code described in Lemma 5.1, hence consecutive children differ in exactly one active half-choice bit. By Lemma 5.2, the endpoint corner of the previous child path and the start corner of the next child path differ along exactly that same bit/axis. By Lemma 5.3, when you interpret those corners as corners of dyadic subboxes in the integer lattice, the corresponding lattice points differ by **exactly 1** in that axis coordinate and are equal in all other coordinates. Therefore the seam step between child paths is a unit lattice step.

Within each child subbox, the path steps are unit steps by the same argument applied at lower levels; thus every step in the full concatenated traversal is a unit step. ∎

### Where activation embedding is used in this proof

The seam argument above depends on “the exit axis is the same physical axis” when you move between levels. In Hamilton’s cube setting, axes are fixed so this is automatic. In the unequal-dimension setting, the active axis list $A_s$ changes with $s$, so the *index* $d\in\mathbb{Z}_{k_s}$ must be reinterpreted as an axis label and reindexed when $A_s$ grows. That is exactly what the activation embedding rule enforces.

Without that reindexing, the premise of Lemma 5.2 fails at the activation seam $this is precisely why (4\times 2) can break if you treat (d) as a raw position rather than a physical axis$.

---

## 6. Summary of proven properties

For every dyadic box $P(m)$:

1. `encode` and `decode` are exact inverses (Theorem 4.4).
2. The traversal $H_m(h)=\mathrm{decode}(h,m)$ visits every lattice point exactly once (bijection).
3. Successive points are unit $L^1$-neighbors (Theorem 5.4), i.e. discrete Hilbert lattice continuity, consistent with the “unit step” locality principle Hamilton emphasizes for Hilbert lattices. 

---

## 7. If you want to extend this to a true continuous curve

What we proved above is a discrete Hamiltonian path on the integer lattice of a dyadic box. To get a continuous map $[0,1]\to [0,1]^{n}$ (or to an unequal-sided rectangle), the standard approach is to take a limit of the polygonal curves obtained by rescaling these lattice paths as the grid is refined indefinitely. In the unequal-dimension context, you need a refinement scheme where *each axis is refined infinitely often* (otherwise the limit is not space-filling in that axis). The activation framework can be used for that, but the proof requires an additional limiting argument (uniform continuity/Cauchy property of the approximants), which is separate from lattice continuity.

---

## Addendum about the Activation Boundary Seam
At the seam level you only need one extra invariant, and then the “activation near the seam” case is automatic.

**Invariant (endpoint preservation across refinement):** once the level‑$s$ subcell has been chosen, all lower levels `$<s$` only refine *inside that subcell* and do not change its already-fixed higher bits. So the fully refined path through a child subcell still begins at that child’s entry corner $e(i)$ and ends at its exit corner $f(i)$ (in the level‑$s$ corner labeling). The seam step is therefore always “exit corner of child $i$ → entry corner of child $i{+}1$” at level $s$, regardless of what happens at level $s{-}1$ and below.

Now consider the “activation + seam adjacent” scenario: the seam occurs at level $s$ $child (i\to i{+}1)$, but the active axis set grows when you descend to level $s{-}1$. The seam itself is governed by Hamilton’s entry/exit constraints:

* $e(i)$ and $f(i)$ differ in exactly one bit: $e(i)\oplus f(i)=2^{d(i)}$. 
* consecutive children are neighbors along one axis: $f(i)\oplus 2^{g(i)}=e(i{+}1)$, equivalently $e(i{+}1)=e(i)\oplus 2^{d(i)}\oplus 2^{g(i)}$.  

**Where embedding matters:** when the active set grows, the *bit-position* $d\in\mathbb{Z}_{k}$ is no longer a stable geometric object unless you interpret it as “the physical axis along which $e$ and $f$ differ.” That axis is exactly what $e\oplus f=2^{d}$ encodes. 
So the embedding step must:

1. embed $e$ by keeping its bits on the same physical axes, and
2. embed $d$ (and the inter-child axis $g$ if you track it explicitly) by **preserving the axis label**: “old axis = $A_{\text{old}}[d]$” and “new index = position of that same axis inside $A_{\text{new}}$.”

With that, the seam step computed at level $s$ is still along the same physical axis after activation, and because the two adjacent subcells meet along that face, the lattice representatives differ by exactly 1 in that coordinate $the usual (2^{s-1}-1\to 2^{s-1}) boundary jump$ and 0 elsewhere.
