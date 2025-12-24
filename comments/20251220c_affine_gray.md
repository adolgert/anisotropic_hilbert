
I asked ChatGPT 5.2 Pro to try to prove the seam with only V_n and not
using the integer index w into sub-hypercubes. It's sort of thinking in that
direction.

## Seam

This section formulates the “seam” constraints without indexing sub-hypercubes
by an integer.  Instead, we index the $2^n$ child sub-hypercubes by their
**coarse location** $u \in V(A)=\mathrm{GF}(2)^A$ (a vertex of the $n$‑cube),
and we take the **Gray code order** to be a Hamiltonian path structure on $V(A)$.

Throughout, $\oplus$ is XOR in $V(A)$ and $\hat e_a$ is the one‑hot basis vector
for axis $a\in A$.

### 1. Gray order as a path relation on $V(A)$ (no integers)

Fix a directed Hamiltonian path on the $n$‑cube graph:

- A distinguished **start** vertex $s \in V(A)$ (for Type‑I / BRGC we take $s=0$).
- A directed “next” relation $\mathsf{Next}(u,v)$ on $V(A)$ such that:
  1. (**Path / Hamiltonian**) each vertex has at most one successor and at most
     one predecessor, and every vertex is reachable from $s$ by iterating
     $\mathsf{Next}$.
  2. (**Gray adjacency**) whenever $\mathsf{Next}(u,v)$ holds, the step
     \[
       \Delta(u,v) := u \oplus v
     \]
     is one‑hot: $\Delta(u,v)=\hat e_a$ for a unique $a\in A$.

So we never speak about “$w$” or “$w+1$”; we only speak about edges
$\mathsf{Next}(u,v)$ and their step vectors $\Delta(u,v)$.

When needed, write $\mathrm{succ}(u)$ for the unique $v$ with $\mathsf{Next}(u,v)$,
and $\mathrm{pred}(u)$ for the unique $p$ with $\mathsf{Next}(p,u)$.

> (Connection to the usual indexed Gray code.)
> If $g:\{0,\dots,2^n-1\}\to V(A)$ is an indexed Gray code, then one can define
> $\mathsf{Next}(u,v)$ to mean “there exists $i$ with $u=g(i)$ and $v=g(i+1)$”.
> After that definition, all lemmas in this section only mention $\mathsf{Next}$,
> not arithmetic on $i$.

### 2. Entry/exit data of each child sub-hypercube

Inside every child sub-hypercube we use the same **base corner traversal**:
a Gray path through the corners of a unit $n$‑cube that enters at $0$ and exits
at $\hat e_{n-1}$ (this is the BRGC corner path in the standard orientation).

For each child located at coarse vertex $u\in V(A)$ we introduce an unknown
affine “orientation map”
\[
  S_u : V(A) \to V(A), \qquad S_u(x)=\pi_u\cdot x \;\oplus\; y_u,
\]
with $\pi_u\in \mathrm{Sym}(A)$ and $y_u\in V(A)$.

Define the **entry corner label** and **exit corner label** (in the parent’s axis
labelling) by
\[
  E(u) := S_u(0)=y_u,
  \qquad
  X(u) := S_u(\hat e_{n-1})=\pi_u(\hat e_{n-1})\oplus y_u.
\]

Boundary condition (start of the Hilbert curve):
\[
  E(s)=0.
\]

### 3. The seam equation (continuity across adjacent sub-hypercubes)

If $\mathsf{Next}(u,v)$, then the curve exits the child at $u$ and enters the child
at $v$ through a shared face.  The axis of that face is exactly the Gray step
$\Delta(u,v)=u\oplus v$ (which is one‑hot), so the seam continuity requirement is:

\[
  \boxed{\mathsf{Next}(u,v)\ \Longrightarrow\ X(u)\oplus E(v) = u\oplus v.}
  \tag{Seam}
\]

Expanding $E(u)=y_u$ and $X(u)=\pi_u(\hat e_{n-1})\oplus y_u$, we get the
translation recurrence:

\[
  \mathsf{Next}(u,v)\ \Longrightarrow\ 
  y_v = y_u\ \oplus\ \pi_u(\hat e_{n-1})\ \oplus\ (u\oplus v).
  \tag{Rec}
\]

It is useful to name the one‑hot vector
\[
  d(u) := \pi_u(\hat e_{n-1}) \in V(A),
\]
which is the **intra sub-hypercube direction** (the unique axis along which the
child’s entry and exit corners differ).  Then (Rec) becomes

\[
  \boxed{\mathsf{Next}(u,v)\ \Longrightarrow\ y_v = y_u \oplus d(u) \oplus (u\oplus v).}
  \tag{Rec'}
\]

This is the index‑free version of Hamilton’s entry-point relation
$e(i+1)=e(i)\oplus 2^{d(i)}\oplus 2^{g(i)}$ (his Equation (1)), with
$u\oplus v$ playing the role of the inter‑subcube step.  (Hamilton distinguishes
the axis labels $d(i)$ and $g(i)$; here we keep the one‑hot vectors directly.)
:contentReference[oaicite:2]{index=2}

### 4. What the seam constraints do *and do not* determine

The seam equations (Seam)/(Rec') constrain only:

- the translations $y_u$ (equivalently the entry labels $E(u)$), and
- the single one‑hot image $d(u)=\pi_u(\hat e_{n-1})$ of the distinguished exit axis.

They do **not** determine the full permutation $\pi_u$ (how the other $n-1$ axes are
mapped).  Different choices of $\pi_u$ that share the same $d(u)$ still satisfy the
seams, but yield different internal orientations of the recursion.

So additional principles are required to pick out a *canonical* Hilbert curve.

### 5. Symmetry as an additional (canonicalizing) constraint

For the binary reflected Gray code (BRGC), the Gray path has a reversal symmetry:
reversing the traversal corresponds to toggling a fixed axis bit.  In Hamilton’s
indexed form this is Lemma 2.4, $gc(2^n-1-i)=gc(i)\oplus 2^{n-1}$; in our $V(A)$
notation it is natural to package this as an involution
\[
  \rho(u) := u \oplus \hat e_{n-1},
\]
which reverses the directed edges of the BRGC path:
\[
  \mathsf{Next}(u,v)\ \Longleftrightarrow\ \mathsf{Next}(\rho(v),\rho(u)).
\]
:contentReference[oaicite:3]{index=3}

A natural “Type‑I Hilbert” symmetry requirement is that walking the Hilbert curve
backwards corresponds to reflecting in the distinguished axis.  In our entry/exit
data this becomes:
\[
  \boxed{E(u) = X(\rho(u))\oplus \hat e_{n-1}.}
  \tag{HilbSym}
\]
This is exactly Hamilton’s symmetry relation between entry and exit sequences
(Lemma 2.6), rewritten without indices. :contentReference[oaicite:4]{index=4}

**Important:** (HilbSym) is not forced by seam adjacency alone; it is an additional
constraint used to select the canonical symmetric Hilbert curve.

### 6. A canonical choice of $d(u)$ without indices (parity along the path)

Hamilton chooses a particularly simple symmetric rule for the intra directions $d(i)$
(Lemma 2.8).  We can state the same rule without indices by using **parity along the
Gray path**.

Define $\mathrm{par}(u)\in\{0,1\}$ to be the parity of the unique path distance from
$s$ to $u$:
- $\mathrm{par}(s)=0$,
- if $\mathsf{Next}(u,v)$ then $\mathrm{par}(v)=\mathrm{par}(u)\oplus 1$.

For vertices with predecessors/successors define the incoming/outgoing Gray steps:
\[
  \Delta^-(u) := \mathrm{pred}(u)\oplus u,
  \qquad
  \Delta^+(u) := u\oplus \mathrm{succ}(u).
\]
These are one‑hot whenever defined.

**Canonical (Hamilton) rule for $d(u)$ (Type‑I / BRGC):**
- if $u=s$ (start), set $d(u):=\Delta^+(u)$,
- if $u$ is the end vertex, set $d(u):=\Delta^-(u)$,
- otherwise:
  \[
    d(u) :=
    \begin{cases}
      \Delta^-(u), & \mathrm{par}(u)=0\ (\text{even}),\\
      \Delta^+(u), & \mathrm{par}(u)=1\ (\text{odd}).
    \end{cases}
  \]
This is the index‑free content of Hamilton’s Lemma 2.8. :contentReference[oaicite:5]{index=5}

With this choice, (Rec') immediately implies a key structural fact:

- If $\mathsf{Next}(u,v)$ and $\mathrm{par}(u)=1$ (odd), then $d(u)=\Delta^+(u)=u\oplus v$,
  hence
  \[
    y_v = y_u \oplus (u\oplus v)\oplus (u\oplus v) = y_u.
  \]
  **So the entry translation does not change on odd steps.**

This is the conceptual (index‑free) reason that Hamilton’s closed form for entry
points “follows the Gray code with the last index bit zeroed out”: the translation
sequence only changes on every other Gray edge, so it effectively traces the even
positions of the Gray ordering.  Hamilton’s Theorem 2.10 gives the corresponding
indexed closed form. :contentReference[oaicite:6]{index=6}

### 7. What remains to choose: the full rotations $\pi_u$

Once you have fixed $d(u)$, the seam constraints force only the single condition
\[
  \pi_u(\hat e_{n-1}) = d(u).
\]
The rest of $\pi_u$ (how it permutes the remaining $n-1$ axes) is still a design
choice.  Hamilton chooses a restricted, convenient family of cube isometries
(bit-rotations and reflections) because it makes the recursive encoder/decoder
compact and compositional.  In this framework, that choice will appear as a
specific canonical way of extending the constraint
$\pi_u(\hat e_{n-1})=d(u)$ to a full $\pi_u\in\mathrm{Sym}(A)$.
:contentReference[oaicite:7]{index=7}
