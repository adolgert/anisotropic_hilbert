### 0. Working model in (V_n)

To stay faithful to Hamilton/Butz Hilbert (binary subdivision), set
[
V_n := \mathbb F_2^n
]
with vector addition (+) meaning bitwise XOR. Let ({\varepsilon_0,\dots,\varepsilon_{n-1}}) be the standard basis, so (\varepsilon_k) has a single (1) in coordinate (k).

Define the **hypercube graph**
[
Q_n := (V_n,;E),\qquad (u,v)\in E \iff u+v=\varepsilon_k \text{ for some }k.
]
A “lattice-continuous” (discrete) Hilbert curve at the vertex level is exactly a Hamiltonian path in (Q_n) (every step flips exactly one coordinate).

Everything below is the same content Hamilton develops (in integer-bit notation) but written as linear/affine algebra in (V_n).  

---

## 1. BRGC as a linear map (G(\beta)=M\beta)

### 1.1 Index vectors and Gray vectors

Let (\beta(i)\in V_n) be the binary vector of the integer (i\in{0,\dots,2^n-1}) in **LSB-first** order:
[
\beta(i) = \big(\mathrm{bit}(i,0),\dots,\mathrm{bit}(i,n-1)\big)^{\mathsf T}.
]

The **binary reflected Gray code (BRGC)** is the map
[
\gamma(i) := \mathrm{gc}(i) = i \oplus (i\gg 1),
]
which Hamilton states as (\mathrm{gc}(i)= i;\text{XOR};(i\text{ shifted right }1)) (Theorem 2.1). 

In (V_n), this is a **linear** map (\gamma(i)=G(\beta(i))) given by an (n\times n) matrix (M) over (\mathbb F_2):
[
G(\beta)=M\beta,\qquad
M :=
\begin{pmatrix}
1&1&0&\cdots&0\
0&1&1&\cdots&0\
\vdots&&\ddots&\ddots&\vdots\
0&\cdots&0&1&1\
0&\cdots&0&0&1
\end{pmatrix}.
]
Equivalently:
[
\gamma_0=\beta_0+\beta_1,;\gamma_1=\beta_1+\beta_2,;\dots,;\gamma_{n-2}=\beta_{n-2}+\beta_{n-1},;\gamma_{n-1}=\beta_{n-1}.
]

### 1.2 Transition axes (g(i)) and palindromic rhythm

Define the “axis of change” sequence (g(i)\in{0,\dots,n-1}) by
[
\gamma(i+1)=\gamma(i)+\varepsilon_{g(i)}.
]
Hamilton proves for BRGC that (g(i)) is the “ruler function” / trailing-set-bits function:
[
g(i)=\mathrm{tsb}(i)
]
(Lemma 2.3). 

And crucially, the transition sequence is **palindromic**:
[
g(i)=g(2^n-2-i)\qquad (0\le i\le 2^n-2)
]
(Corollary 2.5, derived from the reflection construction of BRGC). 

This is exactly your “Palindromic Rhythm” but stated for **transitions**.

---

## 2. Hamilton’s (T) as an affine automorphism of (Q_n)

Hamilton’s transform is (in his notation)
[
T_{(e,d)}(b)=(b\oplus e);\text{rotR}(d+1),
]
where “rotR” is right-bit-rotation (Section 2.1.3). 

In (V_n), “rotation” is a permutation matrix. Let (R_{d+1}\in GL(n,\mathbb F_2)) be the cyclic permutation matrix that rotates coordinates right by (d+1). Then
[
T_{(e,d)}:V_n\to V_n,\qquad
T_{(e,d)}(x)=R_{d+1}(x+e)=R_{d+1}x + R_{d+1}e.
]
So (T_{(e,d)}) is an **affine map** with linear part (R_{d+1}) and translation (R_{d+1}e).

### Key fact: (T_{(e,d)}) preserves lattice adjacency

If (u,v) are adjacent in (Q_n), then (v=u+\varepsilon_k). Applying (T):
[
T(v)-T(u)=R_{d+1}(u+\varepsilon_k+e)+R_{d+1}(u+e)
=R_{d+1}\varepsilon_k
=\varepsilon_{\sigma(k)}
]
for some permutation (\sigma). Thus (T(u)) and (T(v)) are adjacent.

So: **any (T_{(e,d)}) is a graph automorphism of (Q_n).**

### Endpoint normalization (Hamilton Lemma 2.11 in (V_n))

If (f=e+\varepsilon_d) is the exit corner associated to entry (e) and intra-direction (d), then
[
T_{(e,d)}(e)=0,\qquad T_{(e,d)}(f)=\varepsilon_{n-1}
]
because rotation sends (\varepsilon_d\mapsto \varepsilon_{n-1}). This is exactly Hamilton’s “Transformed Entry and Exit Points” lemma. 

**Interpretation:** If you can specify (e(i)) and (d(i)) for each child cube (i), then (T_{(e(i),d(i))}^{-1}) pulls back the canonical BRGC path (from (0) to (\varepsilon_{n-1})) into a path entering at (e(i)) and exiting at (e(i)+\varepsilon_{d(i)}), while staying lattice-continuous inside the child cube.

So the whole problem is: define (e(i)) and (d(i)) so that the child-cube paths glue together.

---

## 3. The three assertions rewritten in (V_n)

Let the (2^n) child subcubes of the parent be visited in BRGC order (\gamma(0),\gamma(1),\dots,\gamma(2^n-1)). Let:

* (e(i)\in V_n): entry vertex (corner) of the (i)-th child cube,
* (f(i)\in V_n): exit vertex of the (i)-th child cube,
* (d(i)\in{0,\dots,n-1}): intra-direction so (f(i)=e(i)+\varepsilon_{d(i)}),
* (g(i)\in{0,\dots,n-1}): inter-direction so the **next** child cube is adjacent along (\varepsilon_{g(i)}).

The basic gluing constraint is Hamilton’s equation (1), rewritten in (V_n):
[
\boxed{;;e(i+1)=e(i)+\varepsilon_{d(i)}+\varepsilon_{g(i)};;}\qquad(0\le i\le 2^n-2)
]
(using (+) for XOR). 

Now your three symmetries become:

---

### (S1) Shadow symmetry (pairwise entry points)

Define the “erase LSB” map on indices:
[
\mathrm{sh}(i):=\left\lfloor\frac{i-1}{2}\right\rfloor\qquad(i\ge 1).
]
Shadow symmetry says: **entry points depend only on (\mathrm{sh}(i))** (so entries occur in pairs). Concretely, there is a sequence (\eta(k)\in V_n) such that
[
e(2k+1)=e(2k+2)=\eta(k)\qquad (0\le k\le 2^{n-1}-1).
]
This is exactly your “doubled” behavior.

Hamilton’s closed form is (\eta(k)=\gamma(2k)), i.e.
[
\boxed{;;e(2k+1)=e(2k+2)=\gamma(2k);;}
]
(Theorem 2.10, written in his integer form). 

---

### (S2) Mirror symmetry (strict alternation of orientation)

“Forward/backward alternation” is most cleanly expressed as a rule for which face the exit corner lies on.

* If child cube (i) is traversed “forward” relative to the inter-cube step, its exit must lie on the face that meets child cube (i+1), i.e. (d(i)=g(i)).
* If child cube (i) is “backward,” its exit must lie on the face that meets child cube (i-1), i.e. (d(i)=g(i-1)).

Strict alternation means this toggles with parity:
[
\boxed{
;;d(0)=0,\quad
d(i)=
\begin{cases}
g(i) & i\equiv 1\pmod 2,\
g(i-1) & i\equiv 0\pmod 2,; i\ge 2.
\end{cases}
}
]
This is Hamilton’s Lemma 2.8 / Theorem 2.9 definition (modulo notation). 

---

### (S3) Palindromic rhythm (for (d))

You asserted:
[
d(i)=d(2^n-1-i).
]
Hamilton derives this symmetry from BRGC reflection properties (Corollary 2.7), and it is consistent with the parity rule above because (g(\cdot)) itself is palindromic. 

---

## 4. Proof that (S1)–(S3) determine a valid lattice-continuous Hilbert gluing

What must be proved to get a lattice-continuous Hilbert curve (at the “child cube graph” level) is precisely:

1. Each child cube has an internal Hamiltonian path from (e(i)) to (f(i)=e(i)+\varepsilon_{d(i)}).
2. Consecutive child cube paths connect by a single lattice edge:
   [
   f(i)+\varepsilon_{g(i)} = e(i+1).
   ]

Item (1) is guaranteed once (e(i)) and (d(i)) are specified, because (T_{(e(i),d(i))}) is a cube automorphism that normalizes endpoints; pulling back the canonical BRGC gives a Hamiltonian path inside the cube. (Section 2 above; Hamilton Lemmas 2.11–2.12.) 

So the real substance is item (2).

---

### Theorem A (Gluing identity)

Assume (S1) and (S2) with the standard BRGC transition axes (g(i)) (Lemma 2.3). Then for all (0\le i\le 2^n-2),
[
e(i+1)=e(i)+\varepsilon_{d(i)}+\varepsilon_{g(i)}.
]
Equivalently, (f(i)+\varepsilon_{g(i)}=e(i+1)), so the exit of cube (i) is adjacent to the entry of cube (i+1).

#### Proof (case split on parity of (i))

**Case 1: (i) is odd.**
Write (i=2k+1). Shadow symmetry (S1) gives (e(i+1)=e(2k+2)=e(2k+1)=e(i)). Therefore the gluing equation becomes
[
0 = \varepsilon_{d(i)}+\varepsilon_{g(i)}.
]
Since basis vectors are equal iff their indices match, this holds iff (d(i)=g(i)), which is exactly mirror symmetry (S2) for odd (i). So the identity holds for all odd (i).

**Case 2: (i) is even.**
Write (i=2k) with (k\ge 1). Then by (S1),
[
e(i)=e(2k)=e(2k-1)=\gamma(2k-2),
\qquad
e(i+1)=e(2k+1)=\gamma(2k).
]
Now use the BRGC two-step relation:
[
\gamma(2k)=\gamma(2k-2)+\varepsilon_{g(2k-2)}+\varepsilon_{g(2k-1)}.
]
But for BRGC, (g(2k-2)=0) because (2k-2) is even and (g(i)=\mathrm{tsb}(i)) (Lemma 2.3). Hence
[
\gamma(2k)=\gamma(2k-2)+\varepsilon_0+\varepsilon_{g(2k-1)}.
]
Therefore
[
e(i+1)=e(i)+\varepsilon_0+\varepsilon_{g(i-1)}.
]
Since (i) is even, mirror symmetry (S2) sets (d(i)=g(i-1)), and also (g(i)=g(2k)=0). So:
[
e(i)+\varepsilon_{d(i)}+\varepsilon_{g(i)}
==========================================

# e(i)+\varepsilon_{g(i-1)}+\varepsilon_0

e(i+1).
]
Thus the identity holds for even (i) as well. ∎

---

### Corollary (All child-cube paths glue to a single Hamiltonian path on the refined lattice)

Define (f(i):=e(i)+\varepsilon_{d(i)}). Then Theorem A implies
[
f(i)+\varepsilon_{g(i)}=e(i+1)
]
so the exit corner of cube (i) is exactly one lattice edge away from the entry corner of cube (i+1). Therefore concatenating the (2^n) child-cube paths yields a lattice-continuous path through the union.

This is precisely the “Exit-to-Entry Adjacency constraint” you cited, but now as an algebraic identity.

---

## 5. Proof that these symmetries are enough to build the full (multi-level) Hilbert curve

Now we prove the usual self-similar statement: the symmetries determine the transforms at each recursion, so the full order-(m) curve is lattice-continuous on the (2^m)-grid.

### Definition (order-(m) discrete Hilbert curve)

Let (L_m := {0,\dots,2^m-1}^n). An order-(m) Hilbert curve is a Hamiltonian path in the grid graph on (L_m) (neighbors differ by (1) in exactly one coordinate).

### Theorem B (Inductive construction)

Assume:

* the top-level child cubes are ordered by BRGC (\gamma(0),\dots,\gamma(2^n-1)),
* the entry points (e(i)) satisfy shadow symmetry (S1),
* intra-directions (d(i)) satisfy mirror symmetry (S2),
* (optionally) (d) satisfies palindromic symmetry (S3) for global self-similarity.

Then the standard recursive construction (“replace each vertex by a scaled copy and transform by (T_{(e(i),d(i))})”) produces a lattice-continuous Hilbert curve in (L_m) for every (m\ge 1).

#### Proof (induction on (m))

**Base (m=1).**
(L_1\cong V_n) and BRGC (\gamma(0)\to\cdots\to\gamma(2^n-1)) is already a Hamiltonian path in (Q_n) by definition.

**Inductive step (m\to m+1).**
Partition (L_{m+1}) into (2^n) subcubes of side (2^m), indexed by (\gamma(i)\in V_n). Each subcube is isomorphic (as a grid graph) to (L_m).

By the inductive hypothesis, there exists a lattice-continuous order-(m) Hilbert path in a canonical orientation (entry (0), exit (\varepsilon_{n-1}) at the “bit-signature level”). Applying the affine cube automorphism (T_{(e(i),d(i))}^{-1}) (lifted to the subcube) maps this canonical path to a lattice-continuous path inside subcube (i) whose entry/exit corners are exactly (e(i)) and (f(i)=e(i)+\varepsilon_{d(i)}). This uses only that (T) is built from coordinate permutations and reflections, hence preserves adjacency (Section 2).

Finally, Theorem A gives the gluing condition (f(i)+\varepsilon_{g(i)}=e(i+1)), so the last vertex of subcube (i)’s path is adjacent to the first vertex of subcube (i+1)’s path by a single grid edge across their shared face.

Thus concatenating the (2^n) subcube paths yields a lattice-continuous Hamiltonian path through all of (L_{m+1}). ∎

---

## 6. Where the “palindrome” (S3) is used

For **continuity**, (S1)+(S2) already force Theorem A (the gluing identity), which is the only nontrivial condition needed to concatenate child curves.

Your palindromic assertion (S3) is the extra condition that makes the construction **self-similar under reversal** (the “unwinding mirrors winding”), matching Hamilton’s Corollary 2.7 symmetry (d(i)=d(2^n-1-i)) derived from BRGC reflection symmetry. 

Concretely, using BRGC’s palindromic (g)-sequence (g(i)=g(2^n-2-i)) (Hamilton Corollary 2.5), the parity-based mirror rule (S2) implies:

* if (i) is odd then (2^n-1-i) is even, so
  [
  d(2^n-1-i)=g(2^n-2-i)=g(i)=d(i),
  ]
* if (i) is even then (2^n-1-i) is odd, so
  [
  d(2^n-1-i)=g(2^n-1-i)=g(i-1)=d(i),
  ]
  giving the palindrome for (d) automatically.

So (S3) is not an additional independent axiom; it is a **consequence** of (S2) plus the palindromic rhythm of BRGC transitions.

---

## 7. Summary of the symmetry-only construction in (V_n)

All data needed to generate the Hilbert recursion is determined by:

1. **BRGC linear map** (\gamma(i)=M\beta(i)) and its transition axes (g(i)). 
2. **Shadow symmetry (pairing):**
   [
   e(0)=0,\quad e(2k+1)=e(2k+2)=\gamma(2k).
   ]
3. **Mirror symmetry (alternation):**
   [
   d(0)=0,\quad d(2k+1)=g(2k+1),\quad d(2k)=g(2k-1)\ (k\ge 1).
   ]
4. **Affine placement transform** per child cube:
   [
   T_{(e(i),d(i))}(x)=R_{d(i)+1}(x+e(i)).
   ]

From these, Theorem A gives the gluing identity, and Theorem B gives lattice continuity at every refinement level.

---

If you want the same development in (V_n=\mathbb F_w^n) with (w>2), the only place the proof changes is the replacement of BRGC by a (w)-ary reflected Gray code (or Peano-type recursion): the “shadow pairing” becomes a (w)-fold repetition under projection, and the automorphism group you need is the affine isometries of the (w)-ary grid rather than bit-rotations/XOR. The structure of Theorems A–B remains the same, but the specific matrix (M) and the transition rule (g(i)) change.
