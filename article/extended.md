# Algebraic Formulation of the Hilbert Curve

## With equal sides

### Setting

 - $n \geq 1$ - Dimension of the space.
 - $m \geq 1$ - Bits per axis of the hypercubic lattice. Each dimension is $2^m$ in extent.
 - A *point* in a lattice has $n$ dimensions where each dimension is in $[0, 2^m-1]$.
 - The Hilbert *index* of a point in in $[0, mn - 1]$.

### Vectors Over GF(2)

The Hilbert curve is recursive. At each level, we think about a hypercube that
has $2^n$ lattice points. We will need to choose a particular lattice point
and rotate the hypercube around it with a permutation. Let's start by defining
a hypercube in $n$ dimensions.

We represent it with a vector space of $V_n=\{0, 1\}^n$ values. We don't treat them as
integers because there is no sense of addition with a carry operation. It is
useful to think of two operations on these vectors of integers.

 - A sort of addition using an XOR, represented by $\oplus$. That is $0\oplus 0=0$,
   $0\oplus 1=1$, $1\oplus 0=1$, and $1\oplus 1=0$.
 - A sort of multiplication using AND, represented by $\otimes$. Here the
   truth table is $0\otimes 0=0$, $0\otimes 1=0$, $1\otimes 0=0$, and $1\otimes 1=1$.

An element $v\in V_n$ is $v=(v_0, v_1, v_2,\ldots)$. Two vectors are adjacent if they differ in exactly one coordinate:
$$u + v = \hat{\mathbf{e}}_j$$
for some standard basis vector $\hat{\mathbf{e}}_j = 2^j$.

We can represent an element of $V_n$ using an integer $\sum_{j=0}^{n-1} v_j2^j$.

### Axis labels

We just snuck in another concept, the labels on the axes of a vector.

 - $A$ is the set of axis labels, $\{0, 1,\ldots,n-1\}$.
 - $V(A) = \mathrm{GF}(2)^A$ so we think of the vector over GF(2) as indexed by axis labels.

This allows us to be specific about, for instance, permutations.
A permutation $\pi \in \mathrm{Sym}(A)$ acts on a bitvector $v \in V(A)$ by relabeling coordinates:
$$
(\pi \cdot v)(a) := v(\pi^{-1}(a))
$$

### Affine maps on $V(A)$


#### Definition

An **affine map** is a function $S: V(A) \to V(A)$ of the form:
$$
S_{y,\pi}(v) := \pi \cdot \mathbf{v} + \mathbf{y}
$$

where $\pi$ is the **linear part**, that is an operation expressible as a matrix, and $\mathbf{y} \in V(A)$ is the **translation**.

We care about affine maps because as we traverse from the most coarse-grained
lattice to the most fine-grained, at each level we will rotate and translate
our frame of reference. For us, the operator $\pi$ will be a rotation,
and $y$ will be the entry point of the Hilbert curve to the sub-lattice.

#### Composition

Let $S_1 = S_{y_1, \pi_1}$ and $S_2 = S_{y_2, \pi_2}$. Then:
$$
(S_1 \circ S_2)(v) = S_1(S_2(v)) = S_1(\pi_2 \cdot v + y_2) = \pi_1 \cdot (\pi_2 \cdot v + y_2) + y_1
$$
$$
= (\pi_1 \circ \pi_2) \cdot v + \pi_1 \cdot y_2 + y_1
$$

So composition is:
$$
\boxed{(e_1, \pi_1) \cdot (y_2, \pi_2) = (y_1 + \pi_1 \cdot y_2, \; \pi_1 \circ \pi_2)}
$$

This is the standard **semidirect product** $V(A) \rtimes \mathrm{Sym}(A)$.

#### Group structure

| Operation | Formula |
|-----------|---------|
| Identity | $(0, \mathrm{id})$ |
| Inverse | $(e, \pi)^{-1} = (\pi^{-1} \cdot e, \; \pi^{-1})$ |
| Composition | $(e_1, \pi_1) \cdot (e_2, \pi_2) = (e_1 + \pi_1 \cdot e_2, \; \pi_1 \circ \pi_2)$ |

**Verification of inverse:**
$(e, \pi) \cdot (\pi^{-1} \cdot e, \pi^{-1}) = (e + \pi \cdot (\pi^{-1} \cdot e), \pi \circ \pi^{-1}) = (e + e, \mathrm{id}) = (0, \mathrm{id})$ ✓

#### The inverse map

If $S_{y,\pi}(v) = \pi \cdot v + y$, then:
$$
S_{y,\pi}^{-1}(w) = \pi^{-1} \cdot (w + y)
$$

**Verification:** $S(S^{-1}(w)) = \pi \cdot (\pi^{-1} \cdot (w + y)) + y = (w + y) + y = w$ ✓

The value at position $a$ in the result comes from position $\pi^{-1}(a)$ in the input.

### Cyclic Rotation

A cyclic rotation $\rho$ is a linear operator on $V_n$ that shifts all components one
position to the right, wrapping around.
$$
    (\rho v)_j = v_{(j-1)\bmod n}
$$

For example, for $n=3$, we could represent a cyclic rotation as a matrix.
$$
\rho = \begin{bmatrix}
0 & 0 & 1 \\
1 & 0 & 0 \\
0 & 1 & 1
\end{bmatrix}
$$

### Gray Code

What is a Gray code (binary case)?
A (binary) Gray code of dimension n is a bijection
$$
g : {0,\ldots,2^n−1} \rightarrow V_n
$$
such that consecutive values differ in exactly one coordinate:
$$
g(i+1) + g(i) = \hat{e}_{a(i)}
$$
for some axis a(i) ∈ A.
Given a particular Gray code, we know the function $a(i)$.


```
\textbf{The BRGC Gray code sequence:}
\begin{center}
\begin{tabular}{c|c|c}
    $i$ & binary & $G(i)$ \\ \hline
    0 & 000 & 000 \\
    1 & 001 & 001 \\
    2 & 010 & 011 \\
    3 & 011 & 010 \\
    4 & 100 & 110 \\
    5 & 101 & 111 \\
    6 & 110 & 101 \\
    7 & 111 & 100
\end{tabular}
\end{center}
```

Equivalently: it’s a Hamiltonian path on the n‑cube (the Cayley graph of V_n with generators {e_0,…,e_{n−1}}).
If you also require g(0) and g(2^n−1) to differ in one bit, it’s a cyclic Gray code (Hamiltonian cycle).

The Binary-reflected Gray code is also a linear operator in $V_n$.


If we think of the input integer as a member of $V_n$, then the Gray code
formula is
$$
 G(v)_j = \begin{cases}
 v_j\oplus v_{j+1} & j < n-1 \\
 v_{n-1} & j = n-1
 \end{cases}
$$
That is, the Gray code is also a linear operation, expressible as a matrix,
when we think of multiplication as AND and addition as XOR.

For $n=3$, here is the matrix form.
$$
G = \begin{bmatrix}
1 & 1 & 0 \\
0 & 1 & 1 \\
0 & 0 & 1
\end{bmatrix}
$$
This matrix has an inverse in this space. For $n=3$,
$$
G^{-1} = \begin{bmatrix}
1 & 1 & 1 \\
0 & 1 & 1 \\
0 & 0 & 1
\end{bmatrix}
$$
As an equation, it's the XOR with previous indices.
$$
(G^{-1}v)_j = \bigoplus_{k=j}^{n-1}v_k
$$

For the BRGC, the difference between the start and finish is a unit vector we label $\hat{e}_{n-1}$
It is always true that:
$$
\begin{align}
 g(0)&=0 \\
 g(0) + g(\mathbf{1}) & = \hat{e}_{n-1}
\end{align}
$$
Recall that $\mathbf{1}$ is equal to the integer $2^n-1$.


We can state the symmetry in $V_n$.
$$
G(\mathbf{v}+\mathbf{1})=G(\mathbf{v})\oplus\mathbf e_{n-1}.
$$
The gray code of the complement is the gray code plus an offset.

We can compute $\hat{e}_{n-1}$ in closed form as the trailing-set-bits of $n$ or
$\text{tsb}(n)$. This is the index of the least-significant 0 in the integer.

## Nested Spaces

Before we discuss encoding or decoding Hilbert indices, let's create the space
in which they live.

The final lattice will have sides of length $2^m$ in $n$ dimensions.
We index this lattice by starting with a coarse lattice of size $2^n$
which we call level 0 and recursively subdivide this lattice $m$ times.

From one level to each child sub-cube, we will take the existing orientation
and apply a rotation and translation to it to get the child's orientation. That
is, we will apply an affine transformation.

The Gray code can number the initial coarse lattice using $n$ bits. These will
be the most-significant bits (or high bits) of the Hilbert index. The next level
will be the next set of Hilbert index bits. Our main challenge is ensuring that,
at the child level, the exit from one of the $2^n$ sub-cubes exits adjacent
to the entrance to the next sub-cube.

We ensure adjacency of sub-cubes by aligning the ordering within sub-cubes
according to which faces are adjacent in the parent level. We call this
alignment "lifting the Gray code." It asks which affine transformation gives
us adjacent points in the sub-cube.

We are going to think about transforming the child spaces to be in the same
orientation as the parent space.

  - Let $V_n^{\text{parent}}$ be the bitspace for the parent cube.
  - Each child (w) has its own local space $V_n^{(w)}$.
  - The orientation map
    $$
    S_w : V_n^{(w)} \to V_n^{\text{parent}}
    $$

There is a nice property of the dyadic box that relates the child adjacency
to orientation in the parent space.

#### Lemma (one‑hot to unit step).
Let two level‑$s$ corners have labels $\ell,\ell'\in V_n$.
If $\ell+\ell'=\mathbf e_a$, then the corresponding level‑0 lattice points differ by $\pm 1$ in coordinate $a$ and by 0 in all other coordinates.

As a result, the seam equation lives in the coarse label space (V_n), not in the fine grid. It does not claim adjacency at that coarse level. It is a proxy that determines the axis of the fine‑scale step. The sign of the step comes from the fact that we are matching exit‑corner to entry‑corner.

## Seam

For the BRGC, the entry is $\mathbf{0}$ and the exit is $\mathbf{e}_{n-1}$ which is a label that may correspond to the last axis or may correspond to any other axis; it's a unit vector specific to this Gray code for this $n$.

When we transform a sub-cube into the parent space with an orientation map, we transform the entry to $E_w=S_w(\mathbf{0})$ and exit to $X_w=S_w(\mathbf{e}_{n-1})$. Here $S_w$ is a set of affine maps indexed by $w$ which is the index of the sub-cube within the parent space. Our job is to determine the unknown $S_w$.

For sub-cube $w=0$, set the boundary condition that $S_0(E_0)=\mathbf{0}$
so that the Hilbert curve will always start at the origin at any resolution.

Consider sub-cube $w$. In the parent space, the direction of movement from sub-cube $w-1$ to $w$ is
$$
 g(w-1) \oplus g(w) = \hat{\mathbf{e}}_{a(w-1)}
$$
and the movement from sub-cube $w$ to $w+1$ is
$$
 g(w) \oplus g(w+1) = \hat{\mathbf{e}}_{a(w)}
$$
This makes the constraints on each side of sub-cube $w$
$$
  X_{w-1} \oplus E_w = \hat{\mathbf{e}}_{a(w-1)}
$$
and
$$
  X_{w} \oplus E_{w+1} = \hat{\mathbf{e}}_{a(w)}
$$
That is, when we take the sub-cube's entry and exit and lift them
into the parent space, they should differ along the same coordinate
as the difference in Gray code of the sub-cubes.

The affine transform, if we write it out, is
$S_w(\mathbf{v})=\pi_w\mathbf{v}+\mathbf{y}_w$.
We said above that $E_w=S_w(0)$, so the transform will translate the entry to
$$
  E_w=y_w,
$$
and it will translate the exit to
$$
  X_w = \pi_w \mathbf{e}_{n-1} + y_w.
$$
Now go back to rewrite our seam constraints.
$$
\begin{align}
X_{w} + E_{w+1} & = \hat{\mathbf{e}}_{a(w)} \\
\pi_w \mathbf{e}_{n-1} + y_w + y_{w+1} & = \hat{\mathbf{e}}_{a(w)}
\end{align}
$$
Another way to write this is to see it as determining the next offset
from the previous one.
$$
  y_{w+1} = y_w \oplus \pi_w e_{n-1} \oplus \hat{e}_{a(w)}
$$
This is a recurrence relation.

Now add a symmetry constraint. We want the sub-cubes of the parent
to have a mirror symmetry. In a dyadic box, a mirror symmetry comes from
flipping one dimension. Here the parent moves from its origin to $e_{n-1}$,
so that's the dimension we would flip on.
$$
    X_{n-1-i} = E_i\oplus e_{n-1}
$$
or we could write this in $V_n$.
$$
  X(\mathbf{v}+\mathbf{1}) = E(\mathbf{v}) \oplus e_{n-1}
$$

### 2.3 Consistency under axis suppression

A key move in the activation proof is to treat a \(k\)-dimensional Hilbert traversal as a \((k{-}1)\)-dimensional traversal by “turning off” one axis (holding it fixed). To make that idea precise—without reference to Gray codes or bit tricks—we isolate a structural property of the **generators**: restricting the \(k\)-dimensional generator to a codimension-1 face should reproduce the \((k{-}1)\)-dimensional generator, up to a rigid reorientation (rotation/reflection).

#### Definition 2.3 (\(k\)-dimensional generator)

Let \(V_k := \{0,1\}^k\) be the vertex set of the unit \(k\)-cube (equivalently: the \(k\)-cube graph).
A **\(k\)-dimensional generator** is a sequence
\[
\mathrm{Gen}_k = (v_0, v_1, \dots, v_{2^k-1}), \qquad v_t \in V_k,
\]
that visits every vertex exactly once and satisfies
\[
d_H(v_t, v_{t+1}) = 1 \quad\text{for all } t,
\]
where \(d_H\) denotes Hamming distance. (Equivalently: \(\mathrm{Gen}_k\) is a Hamiltonian path on the \(k\)-cube graph.)

A **cube reorientation** is any bijection \(\sigma:V_k\to V_k\) that preserves adjacency:
\[
d_H(x,y)=1 \iff d_H(\sigma(x),\sigma(y))=1.
\]
(In the language of Alber–Niedermeier, these are exactly the cube symmetries represented as adjacency-preserving permutations in \(W_I\) for a corner-labeling \(I\).)

We write \(\sigma\cdot \mathrm{Gen}_k\) for the sequence obtained by applying \(\sigma\) to each vertex of \(\mathrm{Gen}_k\) (without changing the time-order).

#### Definition 2.4 (Turning off an axis)

Fix \(k\ge 2\) and an axis index \(j\in\{0,\dots,k-1\}\). Define the “lower” \((k{-}1)\)-face orthogonal to axis \(j\) by
\[
F^0_{k,j} := \{v\in V_k : v_j=0\}.
\]

Given a generator \(\mathrm{Gen}_k=(v_0,\dots,v_{2^k-1})\), define its **face restriction**
\[
\mathrm{Res}_{j}\!\left(\mathrm{Gen}_k\right)
\]
to be the subsequence obtained by deleting from \(\mathrm{Gen}_k\) all vertices with \(v_j=1\), keeping the remaining vertices in their original order. (This subsequence has length \(2^{k-1}\).)

Define the coordinate-deletion map (projection)
\[
\pi_j : F^0_{k,j}\to V_{k-1}
\]
by deleting the \(j\)-th coordinate of a vertex.

The induced \((k{-}1)\)-dimensional traversal obtained by “turning off axis \(j\)” is the projected sequence
\[
\pi_j\bigl(\mathrm{Res}_{j}(\mathrm{Gen}_k)\bigr).
\]

#### Definition 2.5 (Consistency of generators across dimensions)

A family \((\mathrm{Gen}_1,\dots,\mathrm{Gen}_n)\) is **consistent under axis suppression** if for every \(k\ge 2\), every axis \(j\in\{0,\dots,k-1\}\), and every cube reorientation \(\sigma:V_k\to V_k\), there exists a cube reorientation \(\sigma':V_{k-1}\to V_{k-1}\) such that
\[
\pi_j\!\left(\mathrm{Res}_{j}\bigl(\sigma\cdot \mathrm{Gen}_k\bigr)\right)
\;=\;
\sigma'\cdot \mathrm{Gen}_{k-1}
\]
as sequences.

In words: **no matter how the \(k\)-generator is oriented**, if we restrict it to the face where one coordinate is fixed (here: \(0\) in the local coordinates), the traversal we see on that face is exactly an oriented copy of the \((k{-}1)\)-generator.

#### Remark 2.6 (Connection to activation embedding)

At level \(s\), the active axis list \(A_s\) specifies which physical coordinates vary at that level; the remaining coordinates are held fixed, so the traversal lies on a lower-dimensional face. When descending and new axes activate (\(A_s \subset A_{s-1}\)), the algorithm embeds the current state by:
(i) preserving the existing orientation data on shared axes,
(ii) fixing newly activated axes to \(0\) in local coordinates, and
(iii) reindexing direction so it still refers to the same physical axis.

Definition 2.5 is the generator-level hypothesis that makes this embedding “geometrically sound”: it guarantees that the higher-dimensional generator, when restricted to the face where the newly activated coordinates are fixed, reproduces the lower-dimensional generator governing the previous level.
