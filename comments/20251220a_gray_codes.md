  What is a Gray code (binary case)?
  A (binary) Gray code of dimension n is a bijection
  g : {0,…,2^n−1} → V_n
  such that consecutive values differ in exactly one coordinate:
  g(i+1) + g(i) = e_{a(i)} for some axis a(i) ∈ A.

  Equivalently: it’s a Hamiltonian path on the n‑cube (the Cayley graph of V_n with generators {e_0,…,e_{n−1}}).
  If you also require g(0) and g(2^n−1) to differ in one bit, it’s a cyclic Gray code (Hamiltonian cycle).

  So the “group” in the background is V_n (size 2^n), and the generator set has size n. The Gray code is a choice of a generator at each step:
  g(0) = 0,
  g(i+1) = g(i) + e_{a(i)}.

  That sequence a(i) is the “flip‑axis sequence.” There’s no group of size n acting; it’s a path in the Cayley graph.

  ———

  Are there other Gray codes?
  Yes, there are many. Any Hamiltonian path/cycle on the n‑cube is a Gray code. Even just applying hypercube automorphisms to BRGC gives a large family:

  - permute axes (rename coordinates),
  - and/or flip a subset of bits (XOR with a constant).

  Those preserve adjacency. But there are far more Gray codes not isomorphic to BRGC by such automorphisms.

  Example (n=2):
  BRGC: 00, 01, 11, 10
  Another valid Gray code: 00, 10, 11, 01 (just swap axes).
  For n≥3, there are many genuinely different ones.

  ———

  What makes BRGC special?
  It has a set of properties that are extremely convenient (and not shared by most Gray codes):

  1. Closed‑form formula
     g(i) = i ⊕ (i >> 1).
     So it’s computed directly from the integer index.
  2. Linearity over GF(2)
     Viewed as a map G: V_n → V_n,
     G(v) = v + (v shifted right by 1).
     This is a linear automorphism (upper‑bidiagonal matrix).
     Its inverse is the “suffix XOR”:
     G^{-1}(g)j = g_j + g{j+1} + … + g_{n−1}.
     Most Gray codes are not linear maps on V_n.
  3. Reflection recursion
     The length‑2^n sequence is:

  - list of length‑2^{n−1} with leading bit 0,
  - then the same list reversed with leading bit 1.
    This gives a clean inductive structure, which is why it aligns so well with recursive space‑filling curves.

  4. Flip‑axis sequence is tsb
     For BRGC,
     g(i+1) = g(i) + e_{tsb(i)}.
     So the axis that flips is exactly the number of trailing 1s of i (or ctz(i+1)).
     That’s a very strong structural property and is one reason Hamilton’s formulas are so clean.

  ———

  A compact V_n definition that highlights BRGC’s specialness

  - A Gray code is any bijection g with g(i+1)=g(i)+e_{a(i)}.
  - BRGC is the unique Gray code of the form g(i)=G(b(i)) for a fixed linear automorphism G of V_n, with b(i) the binary vector of i in lex order.

  That linear‑map characterization is the one that makes the affine‑map Hilbert formulation work so cleanly: you can move G across affine maps and keep everything algebraic.

  What “defines” a Gray code in V_n terms
  A (binary) Gray code is just a Hamiltonian path on the n‑cube:

  - g : {0,…,2^n−1} → V_n is a bijection
  - g(i+1) + g(i) = e_{a(i)} for some axis a(i) ∈ A

  So the group is V_n (size 2^n) with generators {e_a}. The Gray code is a choice of generator at each step, not an action of a group of size n.

  ———

  What the Hilbert algorithm actually needs
  For lattice adjacency, the proof only uses two facts:

  - The child order is a Gray code, so consecutive child cubes share a face.
  - Affine maps preserve “one‑hot” differences.

  That means: any Gray‑code ordering of the 2^n children gives you the correct seam axis sequence a(i). But to be a self‑similar Hilbert curve, you must also lift that Gray code to
  a coherent family of child orientations.

  In V_n terms, you need a map μ: V_n → Aff(V_n) with:

  - μ(w)(0) = entry corner of child w
  - μ(w)(e_{n−1}) = exit corner of child w
  - exit(w) + entry(w+1) = e_{a(w)} (the Gray seam axis)

  This is the real constraint. The Gray code gives you the seam axes a(w), but you still must solve for μ(w) so the whole curve glues and remains a scaled copy of itself.

  ———

  Why BRGC is special for Hilbert
  BRGC has two properties that make the μ‑lift simple:

  1. Linearity over GF(2)
     G is a linear automorphism V_n → V_n, and the “one‑hot” edges are preserved in the fixed axis basis.
     If you demand both linearity and “one‑hot adjacency in the fixed axis basis,” then G can only differ from BRGC by axis permutation (and possibly a translation). Linearity is
     very restrictive here.
  2. Reflection recursion
     BRGC is defined by:

  - first half: 0 ∘ BRGC(n−1)
  - second half: 1 ∘ reverse(BRGC(n−1))

  That reflection rule is exactly what lets Hamilton pick entry corners by “drop the lowest bit, then Gray code” and keep orientations as simple cyclic rotations. This is why the
  generator μ has closed‑form formulas (the tsb pattern + pairwise entry corners).

  So BRGC is not just “a Gray code”; it is the Gray code whose recursion matches the self‑similar orientation rules with a tiny state (just a rotation index).

  ———

  So: can you generate a family of Hilbert curves from Gray codes?
  Yes, but with a big caveat:

  - Any Gray code gives a valid ordering of subcubes.
  - But only some Gray codes admit a μ‑lift that preserves self‑similarity using a small orientation group (e.g., cyclic rotations).
  - For a generic Gray code, a lift may exist only if you allow a larger symmetry group (full coordinate permutations, maybe reflections), and μ will almost certainly be a lookup
    table, not a clean formula.

  In short:

  - Gray code alone is not enough to define a Hilbert curve.
  - A Hilbert curve is a Gray code + a coherent μ‑lift into Aff(V_n).
  - BRGC is distinguished because its linearity + reflection recursion makes that μ‑lift simple and uniform.

 I'll explain that only axis permutations (and reflections via translations) preserve the Hilbert curve’s lattice adjacency and fit its construction; arbitrary invertible linear
  maps on the bitplanes break the key "one-hot" property so their curves won’t maintain integer-grid adjacency without revising the algorithm and proofs.

─ Worked for 1m 48s ────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────

• Short answer: you can generate a family, but only a small subgroup of GL(n,2) preserves the Hilbert “lattice‑adjacent” proof. If you use arbitrary invertible linear maps on BRGC,
  you generally break the one‑hot property that the Hilbert construction relies on.

  Why the restriction matters
  The Hilbert proof uses this invariant:

  - If two labels differ by a one‑hot vector e_a, then after applying the state map, they still differ by a one‑hot vector (just along a permuted axis).

  That is true only when the linear part is a permutation of axes.
  A general L ∈ GL(n,2) sends one‑hot vectors to multi‑bit vectors, so L(e_a) is not one‑hot. That breaks the seam‑adjacency argument.

  So the safe family is:

  Allowed linear parts for a Hilbert curve on the integer lattice

  - Axis permutations (elements of Sym(A)), i.e., maps that send each basis vector to another basis vector.

  Reflections are not in GL(n,2); they are handled by translations (bitwise complement in an axis), which correspond to reflecting coordinates:
  x_j ↦ (2^m−1) − x_j.

  Resulting family

  - Permute axes (n! options).
  - Reflect any subset of axes (2^n options).
  - Optionally reverse the traversal (index reversal gives another factor 2).

  These are all “the same” Hilbert curve up to cube symmetries, but they are valid and lattice‑adjacent.

  ———

  What if you do apply arbitrary GL(n,2)?
  You still get a Gray code, but you no longer have a Hilbert curve on the integer lattice unless you:

  - enlarge the orientation group to GL(n,2),
  - rewrite the generator μ accordingly,
  - and re‑prove lattice continuity (which will generally fail, because mixing bits across axes does not preserve L1 adjacency).

  ———

  About “pinning one axis”
  Yes — the canonical exit axis e_{n−1} is special in the standard Hilbert construction.
  If you want to “preserve” it, restrict to permutations that fix that axis. That gives the subgroup Sym(A\{n−1}).

  ———

  If you want, I can sketch the precise conjugation formula:

  - given a cube symmetry Φ (axis permutation + reflections), define
    H'(h) = Φ(H(h))
    and show how the Gray code and μ transform under that conjugation.
 Here’s the clean conjugation formula in GF(2)^n language, plus how it induces a family of Hilbert curves.

  Setup (affine maps on V_n)
  Write Aff(V_n) = V_n ⋊ Sym(A).
  An affine map is (t, ψ) acting by v ↦ ψ·v + t, where:

  - t ∈ V_n is translation (bitwise XOR),
  - ψ ∈ Sym(A) permutes axes (linear part).

  The inverse is (t, ψ)^{-1} = (ψ^{-1}·t, ψ^{-1}).

  ———

  Conjugation formula (the key piece)
  Let S = (e, π) be an affine map (v ↦ π·v + e), and let Φ = (t, ψ).

  Then:

  Φ ∘ S ∘ Φ^{-1} = (e', π')
  π' = ψ ∘ π ∘ ψ^{-1}
  e' = t + ψ·e + π'·t

  This is a direct computation using the left action on V_n.

  ———

  Apply this to the Hilbert generator μ
  The generator is μ(w) = (e(w), π(w)).
  Conjugate it by Φ to get a new generator:

  μ^Φ(w) = Φ ∘ μ(w) ∘ Φ^{-1}
  π^Φ(w) = ψ ∘ π(w) ∘ ψ^{-1}
  e^Φ(w) = t + ψ·e(w) + π^Φ(w)·t

  This yields a new Hilbert curve with the same index order but transformed geometry.

  ———

  What curve do you get?
  If H is the original Hilbert curve, then the conjugated generator produces:

  H^Φ = Φ ∘ H

  i.e., you apply the cube symmetry Φ to every point of the curve.

  ———

  Which Φ are “safe”?
  To preserve the lattice‑adjacency proof, ψ must be an axis permutation (so one‑hot vectors stay one‑hot).
  Translations t are always safe (they just flip selected coordinate bits at every level → axis reflections).

  So the symmetry family is:

  - all axis permutations (Sym(A)),
  - all translations in V_n,
    giving 2^n · n! cube symmetries.

  If you want to “pin” the canonical exit axis e_{n−1}, restrict to permutations with ψ(e_{n−1}) = e_{n−1} (the stabilizer subgroup).

• Short answer: yes — a fixed axis permutation is just a global symmetry. If you apply it, you get the same recursion pattern in relabeled coordinates. So you could compute the
  standard curve and rotate axes afterward; it’s equivalent.

  Here’s the precise statement in V_n language:

  Let H be the standard Hilbert curve with generator μ.
  Let Φ = (t, ψ) ∈ Aff(V_n) be a fixed cube symmetry (axis permutation ψ + translation t).
  Define a new curve by:

  H^Φ(h) = Φ(H(h)).

  Then its generator is conjugated:

  μ^Φ(w) = Φ ∘ μ(w) ∘ Φ^{-1}.

  This is exactly “compute H, then rotate/reflect” — not a new internal recursion, just a coordinate change.

  ———

  If you want a genuinely distinct internal pattern, you must change μ not by conjugation. There are two levers:

  1. Change the child order (Gray code).
     A different Hamiltonian path on the n‑cube gives a different seam axis sequence a(w).
  2. Enlarge the allowed permutation group for the linear part.
     Hamilton restricts π(w) to cyclic rotations, which makes it forced:
     π(w)(e_{n−1}) = e_{a(w)} has a unique solution inside the cyclic subgroup.
     If you allow full Sym(A), then for each w there are (n−1)! permutations that send e_{n−1} to the seam axis. That’s real freedom and yields different recursion patterns.

  So: global axis rotation = no new internal pattern.
  New internal pattern = different μ, which means either a different Gray code, or a larger orientation group than cyclic rotations (with more state / lookup).

  If you want, I can sketch a “degrees‑of‑freedom” lemma you can drop into article/extended.md that makes this precise.
  Degrees‑of‑Freedom Lemma (Hilbert generators)

  Fix dimension n and let A = {0,…,n−1}, V_n = GF(2)^A.
  A Hilbert generator is a map

  μ : V_n → Aff(V_n),     μ(w) = (e(w), π(w))

  that satisfies the seam‑gluing constraints:

  1. Entry/exit of each child
     Each child curve is a canonical path from 0 to e_{n−1}.
     So after applying μ(w), its exit axis must be the seam axis a(w):

  π(w)(e_{n−1}) = e_{a(w)}.

  2. Seam adjacency
     If the child order is a Gray code g, then:

  g(w) + g(w+1) = e_{a(w)}.

  So a(w) is determined solely by the Gray code.

  ———

  Consequences

  - The Gray code fixes the seam axis sequence a(w).
  - For each w, the condition π(w)(e_{n−1}) = e_{a(w)} is a constraint on the permutation.

  If the allowed linear parts are only cyclic rotations, then there is a unique π(w) satisfying that constraint.
  So the generator μ is fully determined by the Gray code (up to conjugation).

  If the allowed linear parts are all of Sym(A), then for each w there are

  |(Sym(A))_{e_{n−1}→e_{a(w)}}| = (n−1)!

  choices of π(w), because you can permute the remaining axes arbitrarily once the exit axis is fixed.

  So:

  - Gray code choice = global degrees of freedom (changes seam axes).
  - Permutation group size = local degrees of freedom at each child (changes internal recursion).

  ———

  Interpretation

  - A global symmetry Φ gives a conjugate generator μ^Φ — this does not change internal recursion (only relabels axes).
  - A new internal pattern requires changing μ outside conjugation, which is only possible if:
      - you change the Gray code, or
      - you allow a larger permutation group than cyclic rotations.


Short answer: if you insist on linearity over GF(2) then, up to axis permutation (and translation), the only Gray code is BRGC. So you won’t get new internal patterns and a
  closed‑form linear Gray code.

  Here’s the clean V_n argument.

  ———

  Lemma: linear Gray codes are BRGC up to axis permutation
  Let b(i) ∈ V_n be the binary vector of i (LSB = axis 0). Define

  p_k := e_0 + e_1 + … + e_k   (0 ≤ k ≤ n−1)

  Fact about binary increment:

  b(i+1) + b(i) = p_{tsb(i)}.

  (You flip a block of trailing 1s to 0 and the next 0 to 1, so the difference is a prefix of ones.)

  Now suppose g(i) = L b(i) with L : V_n → V_n linear, and g is a Gray code. Then:

  g(i+1) + g(i) = L(b(i+1)+b(i)) = L(p_{tsb(i)})

  Gray adjacency means this must be one‑hot for every i. Therefore:

  L(p_k) = e_{σ(k)}   for some permutation σ of {0,…,n−1}.

  But {p_0,…,p_{n−1}} is a basis of V_n, so this uniquely determines L.
  That linear map is exactly:

  L = P ∘ G

  where G is the BRGC linear map and P is a permutation of axes.
  (Translations don’t affect differences, so they just shift the code.)

  So: linear + Gray ⇒ BRGC up to axis permutation (and translation).

  ———

  Implication for Hilbert families
  If you want:

  - lattice adjacency in the standard axis basis, and
  - a closed‑form linear Gray code,

  then you’re essentially locked into BRGC (up to global symmetry), which doesn’t change the internal recursion pattern.

  To get genuinely new internal patterns, you must relax something:

  1. Drop linearity of the Gray code.
     Then you can generate other Gray codes, but μ won’t have the same closed‑form structure; you’ll likely need recursive rules or tables.
  2. Enlarge the orientation group (allow full Sym(A) or reflections).
     That gives many new μ choices, but again, closed‑forms like BRGC typically disappear.

  So the trade‑off is real:
  closed‑form + linearity ⇒ essentially BRGC;
  new internal pattern ⇒ more complicated μ.

## Constraints

Yes — your instinct is right. In 2D you do need both seams to pin the orientation, and the “solution” is exactly a tiny affine‑map equation in ($V_2$).

  Here is a clean 2D derivation in ($V_2 = \mathrm{GF}(2)^2$):

  Let ($A=\{0,1\}$) and let the child order be BRGC:
  $(g(0),g(1),g(2),g(3) = 00,01,11,10)$.
  The seam axis between child $(w)$ and $(w+1)$ is
  $$
  g(w)+g(w+1) = \mathbf e_{a(w)}.
  $$
  So $(a(0)=0,; a(1)=1,; a(2)=0)$.

  Each child is a canonical 2D Hilbert path from (0) to $\mathbf e_1$.
  An oriented child is an affine map
  $$
  S_{e,\pi}(v)=\pi\cdot v + e,
  $$
  so:

  - entry corner = $S(0)=e$,
  - exit corner = $S(\mathbf e_1)=\pi\mathbf e_1 + e$.

  Seam constraints are:

  1. Exit axis must be the seam axis:
     $$
     \pi(\mathbf e_1)=\mathbf e_{a(w)}.
     $$
  2. Entry corner must be adjacent to the previous exit:
     $$
     \text{entry}(w) = \text{exit}(w-1) + \mathbf e_{a(w-1)}.
     $$

  In 2D, $\pi$ is just a swap or identity:

  - If $a(w)=1$, then $\pi=I$.
  - If $a(w)=0$, then 
$$
  \pi=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$
  That’s the “little matrix equation.”
  Once $\pi$ is fixed by the exit seam, the entry seam fixes (e).

  So the ambiguity you’re seeing (“two choices on the face between child 0 and 1”) is real when you only look at that single seam. The second seam (between child 1 and 2) forces
  the exit axis, which forces $\pi$, which then forces the entry corner (e).

  This is exactly what Hamilton’s generator $\mu(w)=(e(w),\pi(w))$ encodes:

  - $\pi(w)$ is fixed by the seam axis $a(w)) via (\pi(w)\mathbf e_1=\mathbf e_{a(w)}$.
  - $e(w)$ is the unique entry corner that makes the previous seam glue; in closed form it is
    $$
    e(w)=G(P(b(w-1)))
    $$
    where (P) zeroes the axis‑0 bit. In 2D that yields the “pairwise constant” entry pattern you see in the U‑turn.

  So yes: “looking at the interface between 1 and 2” is exactly the correct way to disambiguate the orientation of child 1. The Hilbert generator is the compact way to encode that
  pair of constraints at each child.

Can you write the seam equation as a constraint on sub-cube w given the parent Hilbert relations for w-1, w, and w+1? Is the right way to think about the degrees of freedom that

  a sub-cube's exact adjacency is pinned by its two neighbors?
• Yes — you can write the seam constraints exactly as affine equations in (V_n), and it’s fair to say “child (w) is pinned by its two neighbors” (with the endpoints pinned by
  global boundary conditions).

  Here’s the clean formulation.

  Definitions (in $V_n$)

  - Gray order: $g(w) = G(b(w))$.
  - Seam axis: $g(w)+g(w+1) = \mathbf e_{a(w)}$.
  - Child orientation: $S_w(v) = \pi_w \cdot v + e_w$.
  - Entry/exit corners of child (w):
    $$
    E_w := S_w(0) = e_w,\qquad
    X_w := S_w(\mathbf e_{n-1}) = \pi_w \mathbf e_{n-1} + e_w.
    $$

  Seam equations (parent adjacency)
  $$
  X_{w-1} + E_w = \mathbf e_{a(w-1)},\qquad
  X_w + E_{w+1} = \mathbf e_{a(w)}.
  $$

  These are the two “neighbor” constraints: the entry of (w) must be adjacent to the exit of (w-1), and the exit of (w) must be adjacent to the entry of (w+1).

  As constraints on (S_w)
  From the seam between (w) and (w+1):
  $$
  \pi_w \mathbf e_{n-1} = \mathbf e_{a(w)}.
  $$
  From the seam between (w-1) and (w):
  $$
  e_w = X_{w-1} + \mathbf e_{a(w-1)}.
  $$

  So:

  - Exit seam fixes the linear part (\pi_w).
  - Entry seam fixes the translation (e_w).

  That’s the “little matrix equation”: $\pi_w \mathbf e_{n-1} = \mathbf e_{a(w)}$, where (\pi_w) is a permutation matrix.

  Degrees of freedom

  - If you restrict (\pi_w) to the cyclic rotations (Hamilton’s setting), the equation $\pi_w \mathbf e_{n-1} = \mathbf e_{a(w)}$ has exactly one solution. Then (e_w) is forced by
    the previous seam. So child (w) is pinned by its two neighbors.
  - If yoeEu allow the full (\mathrm{Sym}(A)), the same equation has ((n-1)!) solutions (permute the remaining axes), so you get genuine internal freedom.

  Endpoints
  For (w=0), the entry corner is fixed globally to (0).
  For (w=2^n-1), the exit corner is fixed globally to (\mathbf e_{n-1}).

  So yes: in the interior, the exact orientation of each sub‑cube is pinned by the two neighboring seams; the equations above are the precise GF(2)(^n) statement of that.


   I'm concerned that these equations are mixing spaces. We have been using V_n which is GF(2)^n to represent the parent space, and we have been using to to represent each child
  space. When you wrote above that X_{w-1} + E_w = e_{a(w-1)}, the X_{w-1} is in the child space of the w-1 child, and E_w is the in the child space of the w child. Can you
  clarify the same explanation you gave above? And I would love it if you used  to delimit equations on their own line and  for inline equations.


• You’re right to flag that. The fix is to be explicit about which copy of (V_n) we’re in at each step.

  Two copies of (V_n)

  - Let $V_n^{\text{parent}}$ be the bitspace for the parent cube.
  - Each child (w) has its own local space $V_n^{(w)}$.
  - The orientation map
    $$
    S_w : V_n^{(w)} \to V_n^{\text{parent}}
    $$
    is an affine isomorphism. So entry/exit corners live in the parent space:
    $$
    E_w := S_w(0) \in V_n^{\text{parent}},\qquad
    X_w := S_w(\mathbf e_{n-1}) \in V_n^{\text{parent}}.
    $$

  So the seam equation is not mixing spaces; it is entirely in the parent space:
  $$
  X_{w-1} + E_w = \mathbf e_{a(w-1)} \in V_n^{\text{parent}}.
  $$

  Everything on that line is in the parent’s $V_n$.

  ———

  Same seam constraints, now fully typed

  Let (g(w)) be the Gray code in the parent indexing, so
  $$
  g(w)+g(w+1)=\mathbf e_{a(w)} \in V_n^{\text{parent}}.
  $$

  The seam constraints are:
  $$
  X_{w-1} + E_w = \mathbf e_{a(w-1)},\qquad
  X_w + E_{w+1} = \mathbf e_{a(w)}.
  $$

  And with $S_w(v)=\pi_w\cdot v + e_w$ we have:
  $$
  E_w = e_w,\qquad
  X_w = \pi_w\cdot \mathbf e_{n-1} + e_w,
  $$
  all in $V_n^{\text{parent}}$.

  ———

  What each constraint fixes

  - From the seam between (w) and (w+1):
    $$
    \pi_w \cdot \mathbf e_{n-1} = \mathbf e_{a(w)}.
    $$
    This fixes the linear part (\pi_w).
  - From the seam between (w-1) and (w):
    $$
    e_w = X_{w-1} + \mathbf e_{a(w-1)}.
    $$
    This fixes the translation (e_w).

  So “child (w) is pinned by its two neighbors” is accurate, once you view all seams after embedding into the parent’s space via (S_w).


That's interesting. It's a bit of a lie. The continuity happens at the next level down. If you say you transform the child into the parent space and then enforce continuity, it
  wouldn't normally be true that neighbors in the parent space are neighbors at the next level down, except that, for an n-dimensional cube represented by GF(2)^n, there is no
  sign on the e_{a(w)} that defines a neighbor. Like, literally, look at $X_{w-1}+E_w=e_{a(w-1}$. If that is in the parent space, then it's a statement about neighbors at that
  level, and we aren't trying to make a statement about the parent space. That statement just happens to coincide with what we want to say about the child space. Do you see that?
  Or am I missing something?


• Yes — I see what you’re getting at. The seam condition is stated in the parent’s (V_n), but the actual lattice‑continuity claim is about the fine grid, i.e., one level down (and
  all the way to the leaves). The reason the parent‑level “one‑hot XOR” statement is meaningful is not because adjacency happens at that coarse level, but because of a special
  property of the dyadic cube geometry: a one‑hot difference at level (s) expands to a single ±1 step at level (s-1) when you look at the corresponding corner points.

  So the seam equation is a symbolic proxy for fine‑scale adjacency.

  Here’s a precise way to say it, without mixing levels:

  ———

  ## 1) What the seam equation actually encodes

  At level (s), each corner label $\ell \in V_n$ stands for the coarse corner of a subcube at scale $2^{s-1}$. When you go one level down, each coarse corner expands to a whole
  $2^{s-1}$-sized block of fine points. The seam you care about is between the exit corner of child (w-1) and the entry corner of child (w), but evaluated at the finest scale
  inside those two subcubes.

  The equation
  $$
  X_{w-1} + E_w = \mathbf e_{a(w-1)}
  $$
  is a statement in the coarse label space (V_n). It says “these two coarse corners differ in exactly one axis bit.” That does not itself say “the fine points are adjacent.” The
  missing step is:

  > If two coarse corners differ by $\mathbf e_a$, then the corresponding fine‑scale corners differ by exactly $\pm 1$ along axis (a).

  This is exactly the dyadic‑cube lemma used in the discrete proof: one‑hot XOR in the plane labels is what guarantees unit $L^1$ steps at the finest lattice scale.

  So the seam equation is not a claim about adjacency at the parent level; it is the symbolic condition that guarantees adjacency after you expand the cubes.

  ———

  ## 2) Why “no sign” is not a bug

  You noticed that (V_n) only sees $\mathbf e_a$, not the sign. That’s correct. The sign comes from which corner of the subcube you are talking about (entry vs exit), not from the
  bit label itself.

  In other words:

  - the equation $X_{w-1}+E_w=\mathbf e_a$ tells you which axis changes;
  - the fact that it is exit corner vs entry corner tells you the direction of the ±1 step.

  This is why the proof works: the (V_n) statement only needs to fix the axis, because the sign is fixed by the geometry of “exit” vs “entry” in the subcube.

  ———

  ## 3) A concise way to phrase this in your notes

  You could say:

  > The seam equation lives in the coarse label space (V_n), not in the fine grid.
  > It does not claim adjacency at that coarse level.
  > It is a proxy that determines the axis of the fine‑scale step.
  > The sign of the step comes from the fact that we are matching exit‑corner to entry‑corner.

  If you want a single lemma:

  > Lemma (one‑hot to unit step).
  > Let two level‑(s) corners have labels $\ell,\ell'\in V_n$.
  > If $\ell+\ell'=\mathbf e_a$, then the corresponding level‑(0) lattice points differ by (\pm 1) in coordinate (a) and by (0) in all other coordinates.

  That is the clean bridge between the parent‑level (V_n) equation and the lattice adjacency you actually want.

  ———

  So you’re not missing anything — your “this is a bit of a lie” intuition is spot‑on. The seam equation is not literally adjacency at that level; it’s the combinatorial condition
  that guarantees adjacency after refinement.


### Doing the proof

• You’re very close, and your substitutions are correct. The main thing is to be explicit that all seam equations live in the parent space because we push each child’s local
  corners into the parent via $S_w$. I’ll walk it through using your notation and keep basis vectors as $\mathbf e_a$ (to avoid confusion with the translation $e_w$).

  ———

  ## 1) Types and spaces (explicit)

  Each child has its own local copy $V_n^{(w)}$.
  The affine map
  $$
  S_w: V_n^{(w)} \to V_n^{\text{parent}}
  $$
  puts the child into the parent.

  So the entry/exit corners are parent‑space points:
  $$
  E_w = S_w(0),\qquad X_w = S_w(\mathbf e_{n-1}) \quad\in V_n^{\text{parent}}.
  $$

  The Gray code is also in the parent indexing:
  $$
  g(w-1)+g(w)=\mathbf e_{a(w-1)},\qquad g(w)+g(w+1)=\mathbf e_{a(w)}.
  $$

  Thus the seam constraints are correctly written in the parent space:
  $$
  X_{w-1}+E_w=\mathbf e_{a(w-1)},\qquad
  X_w+E_{w+1}=\mathbf e_{a(w)}.
  $$

  ———

  ## 2) Substitute the affine form

  Write
  $$
  S_w(v)=\pi_w\cdot v + e_w.
  $$
  Then
  $$
  E_w=S_w(0)=e_w,
  $$
  and
  $$
  X_w=S_w(\mathbf e_{n-1})=\pi_w\mathbf e_{n-1}+e_w.
  $$

  Plugging into your two seam equations gives exactly:

  First seam:
  $$
  X_{w-1}+E_w=\mathbf e_{a(w-1)}
  $$
  $$
  \pi_{w-1}\mathbf e_{n-1}+e_{w-1}+e_w=\mathbf e_{a(w-1)}.
  $$

  Second seam:
  $$
  X_w+E_{w+1}=\mathbf e_{a(w)}
  $$
  $$
  \pi_w\mathbf e_{n-1}+e_w+e_{w+1}=\mathbf e_{a(w)}.
  $$

  So your substitutions are right.

  ———

  ## 3) Make the constraint clearer (rename the exit axis)

  Let
  $$
  u_w := \pi_w\mathbf e_{n-1}\in{\mathbf e_0,\dots,\mathbf e_{n-1}}.
  $$
  (This is the exit displacement inside child $w$, seen in the parent frame.)

  Then the seam equations become the linear system:
  $$
  u_{w-1}+e_{w-1}+e_w=\mathbf e_{a(w-1)},
  $$
  $$
  u_w+e_w+e_{w+1}=\mathbf e_{a(w)}.
  $$

  Now you can read them as:

  - Given $u_{w-1}$ and $e_{w-1}$, the first seam fixes $e_w$:
    $$
    e_w=\mathbf e_{a(w-1)}+u_{w-1}+e_{w-1}.
    $$
  - Given $e_w$ and $e_{w+1}$, the second seam fixes $u_w$:
    $$
    u_w=\mathbf e_{a(w)}+e_w+e_{w+1}.
    $$

  This is the clean “seam system” in $V_n$.

  ———

  ## 4) Where Hamilton’s formulas come from

  Hamilton’s $e(w)$ has the special property
  $$
  e_{2k+1}=e_{2k+2},
  $$
  i.e. pairwise constant on odd/even pairs.

  If $w$ is odd, then $e_{w+1}=e_w$, so the second seam gives
  $$
  u_w=\mathbf e_{a(w)}.
  $$
  So for odd $w$, the exit axis is exactly the seam axis to the next child.

  If $w$ is even, then $w-1$ is odd, and the first seam gives
  $$
  u_{w-1}=\mathbf e_{a(w-1)}.
  $$
  So for even $w$, the exit axis of the previous child matches the seam axis into $w$.

  That is exactly Hamilton’s parity rule for $d(w)$:

  - odd $w$ uses $a(w)=\mathrm{tsb}(w)$,
  - even $w$ uses $a(w-1)=\mathrm{tsb}(w-1)$.

  So the seam equations plus the pairwise‑constant entry sequence explain the parity split in $d(w)$.

  ———

  ## 5) The key idea to take away

  Your seam equations are correct. They do not immediately pin $\pi_w$ from $\mathbf e_{a(w)}$ alone; instead they relate:

  - the exit axis $u_w$,
  - the entry translations $e_w$ and $e_{w+1}$,
  - the seam axis $\mathbf e_{a(w)}$.

  Hamilton’s specific formulas are one consistent solution of this linear system with the extra design choice that $e(w)$ is pairwise constant. That design choice is what makes the
  generator have a closed form.

  If you want, I can also show explicitly how $e(w)=G(2\lfloor(w-1)/2\rfloor)$ enforces those pairwise constants in $V_n$ language.

### Derive the pairwise constants

Here’s the explicit derivation in (V_n) language.

  Recall:

  - (b(k)\in V_n) is the binary vector of integer (k).
  - The BRGC map (G:V_n\to V_n) is linear.
  - For (w>0),
    $$
    e(w)=G!\left(2\left\lfloor\frac{w-1}{2}\right\rfloor\right).
    $$

  Let
  $$
  k=\left\lfloor\frac{w-1}{2}\right\rfloor.
  $$
  Then
  $$
  e(w)=G(2k).
  $$

  Now compare odd/even pairs.
  Take any (t\ge 1). Then:

  - For (w=2t-1):
    $$
    \left\lfloor\frac{(2t-1)-1}{2}\right\rfloor
    = \left\lfloor\frac{2t-2}{2}\right\rfloor
    = t-1,
    $$
    so
    $$
    e(2t-1)=G(2(t-1)).
    $$
  - For (w=2t):
    $$
    \left\lfloor\frac{(2t)-1}{2}\right\rfloor
    = \left\lfloor\frac{2t-1}{2}\right\rfloor
    = t-1,
    $$
    so
    $$
    e(2t)=G(2(t-1)).
    $$

  Therefore,
  $$
  e(2t-1)=e(2t)\quad\text{for all }t\ge 1.
  $$

  That is the “pairwise constant” property in its cleanest form.

  ———

  Same statement, more “(V_n)” flavored

  Multiplying by 2 means “shift left one bit,” i.e. set the axis‑0 bit to 0.
  Define the projection
  $$
  P:V_n\to V_n,\qquad P(v)_0=0,; P(v)_j=v_j\ (j\ge 1).
  $$

  Then for (w>0):
  $$
  2\left\lfloor\frac{w-1}{2}\right\rfloor
  \quad\text{is exactly}\quad
  P(b(w-1))
  $$
  (viewed as an integer).

  So you can write:
  $$
  e(w)=G(P(b(w-1)))\qquad(w>0),
  $$
  which makes the pairwise constancy obvious: (b(w-1)) and (b(w)) differ only in axis 0 when (w) is odd/even, and (P) kills that difference.


### Again slowly
  The Setup: Unknowns and Knowns                                                                                               
                                                                                                                               
  Knowns (from the Gray code / geometry):                                                                                      
  - The seam axes $a(w)$ for each $w$: these come from $g(w) + g(w+1) = \mathbf{e}_{a(w)}$                                     
  - The boundary condition: $e_0 = 0$ (we start at corner 0)                                                                   
                                                                                                                               
  Unknowns (what we need to solve for):                                                                                        
  - Each child's entry translation $e_w \in V_n$                                                                               
  - Each child's exit axis $u_w = \pi_w \cdot \mathbf{e}_{n-1} \in \mathbf{e}0, \ldots, \mathbf{e}{n-1}$                       
                                                                                                                               
  The constraint equations (one per seam):                                                                                     
  $$u_w + e_w + e_{w+1} = \mathbf{e}_{a(w)}$$                                                                                  
                                                                                                                               
  ---                                                                                                                          
  Counting: Are we under-determined?                                                                                                       
  We have:                                                                                                                     
  - $2^n$ children, each with unknowns $(e_w, u_w)$: that's $2 \cdot 2^n$ unknowns                                             
  - $2^n - 1$ seam equations                                                                                                   
  - 1 boundary condition ($e_0 = 0$)                                                                                           
                                                                                                                               
  So we have $2^n$ equations but $2 \cdot 2^n$ unknowns. We're under-determined by $2^n$ degrees of freedom.                   
                                                                                                                               
  This means: the seam equations alone don't uniquely pin down the solution. We need additional design choices.                
                                                                                                                               
  ---                                                                                                                          
  Hamilton's Design Choice: The Entry Formula                                                                                  
                                                                                                                               
  Hamilton makes a specific choice for $e_w$:                                                                                  
  $$e(0) = 0, \quad e(w) = G\left(b\left(2\left\lfloor\frac{w-1}{2}\right\rfloor\right)\right) \text{ for } w > 0$$            
                                                                                                                               
  This formula has a special property: entries are pairwise constant in a staggered way:                                       
  $$e(1) = e(2), \quad e(3) = e(4), \quad e(5) = e(6), \ldots$$                                                                
                                                                                                                               
  (Note: it's $e(\text{odd}) = e(\text{next even})$, not $e(\text{even}) = e(\text{odd})$.)                                    
                                                                                                                               
  ---                                                                                                                          
  How the Seam Equations Then Determine $u_w$                                                                                  
                                                                                                                               
  Once we fix all the $e_w$ values, each seam equation becomes:                                                                
  $$u_w = \mathbf{e}{a(w)} + e_w + e{w+1}$$                                                                                    
                                                                                                                               
  This is now solved: $u_w$ is uniquely determined by the known quantities on the right.                                       
                                                                                                                               
  Example for $n = 2$:                                                                                                         
                                                                                                                               
  The Gray code gives: $a(0) = 0$, $a(1) = 1$, $a(2) = 0$.                                                                     
                                                                                                                               
  Hamilton's entries: $e_0 = e_1 = e_2 = (0,0)$, $e_3 = (1,1)$.                                                                
                                                                                                                               
  Seam equations solve to:                                                                                                     
  - $u_0 = \mathbf{e}_0 + (0,0) + (0,0) = \mathbf{e}_0$ → exit axis 0                                                          
  - $u_1 = \mathbf{e}_1 + (0,0) + (0,0) = \mathbf{e}_1$ → exit axis 1                                                          
  - $u_2 = \mathbf{e}_0 + (0,0) + (1,1) = (1,0) + (1,1) = (0,1) = \mathbf{e}_1$ → exit axis 1                                  
                                                                                                                               
  ---                                                                                                                          
  Why the Pairwise Constant Property Helps                                                                                     
                                                                                                                               
  When $e_w = e_{w+1}$ (which happens for odd $w$ in Hamilton's scheme), the seam equation simplifies:                         
  $$u_w + e_w + e_w = \mathbf{e}{a(w)}$$                                                                                       
  $$u_w = \mathbf{e}{a(w)}$$                                                                                                   
                                                                                                                               
  So for odd $w$, the exit axis equals the seam axis directly. No computation needed.                                          
                                                                                                                               
  For even $w$, we use the full equation with the (now-known) entries.                                                         
                                                                                                                               
  ---                                                                                                                          
  Summary: The Solution Process                                                                                                
                                                                                                                               
  1. Fix boundary: $e_0 = 0$                                                                                                   
  2. Choose entries: Use Hamilton's formula $e(w) = G(b(2\lfloor(w-1)/2\rfloor))$                                              
  3. Solve for exits: Each $u_w = \mathbf{e}{a(w)} + e_w + e{w+1}$ is now determined                                           
  4. Recover rotations: $\pi_w$ is the unique cyclic rotation with $\pi_w \cdot \mathbf{e}_{n-1} = u_w$                        
                                                                                                                               
  The entry formula is not forced—it's Hamilton's design choice. But once made, the seam equations become a linear system that 
  uniquely determines everything else.                                                             

## From Lean
 1. The Seam Equations and the Class of Solutions

  You are exactly right that the fundamental constraint comes from ensuring the exit of sub-cube w-1 is adjacent to the entry of sub-cube w. Your seam equation is nearly
  correct, but let's write it in the notation of the refine_pi.md document, where $S_w(\mathbf{v}) = \pi_w \cdot \mathbf{v} + \mathbf{y}_w$.

  The exit of the canonical curve is $\mathbf{e}0$ (the first basis vector, not $\mathbf{e}{n-1}$ as in your notes). So, the exit of the transformed curve in sub-cube $w-1$ is
  $X_{w-1} = \pi_{w-1} \cdot \mathbf{e}0 + \mathbf{y}{w-1}$. The entry of the curve in sub-cube $w$ is $E_w = \mathbf{y}_w$.

  The physical locations of these points are relative to their sub-cube's origin, which is at position $G(w-1)$ and $G(w)$ respectively. So the adjacency requirement is:
  $$ (G(w-1) + X_{w-1}) + (G(w) + E_w) = \mathbf{e}_{a(w-1)} $$
  where $a(w-1)$ is the axis of transition between $G(w-1)$ and $G(w)$.

  Rearranging and using $G(w-1) + G(w) = \mathbf{e}_{a(w-1)}$, we get:
  $$ X_{w-1} + E_w = \mathbf{0} $$
  $$ (\pi_{w-1} \cdot \mathbf{e}_0 + \mathbf{y}_{w-1}) + \mathbf{y}_w = \mathbf{0} $$
  This gives us a recurrence relation for the translation vector $\mathbf{y}_w$:
  $$ \mathbf{y}w = \mathbf{y}{w-1} + \pi_{w-1} \cdot \mathbf{e}_0 $$

  This recurrence relation, along with the base case $\mathbf{y}_0 = \mathbf{0}$, defines the **class of possible solutions** for the translation vectors. The solution for any
  $\mathbf{y}_w$ depends entirely on the choice of permutations $\pi_0, \pi_1, \dots, \pi_{w-1}$.

  2. Choosing a Specific Solution: The Role of Symmetry

  As you noted, this system is underdetermined. We need more constraints to fix a specific solution for the permutations $\pi_w$. The Lean proof, following the logic of the
  Hilbert curve, imposes an additional symmetry constraint.

  The constraint is not $y_w = y_{w+1}$, but something much more profound. It relates to the two halves of the curve. The transformation applied to the second half of the
  sub-cubes should be a "reflection" of the transformation applied to the first half.

  A key choice that satisfies the necessary constraints and produces the desired symmetries is to define the permutation $\pi_w$ based on the axes of entry and exit, as we
  discussed previously. Let $d(w)$ be the direction function derived from `tsb()`. We choose $\pi_w$ to be the rotation that aligns the canonical curve's axes with the
  entry/exit axes of sub-cube $w$.
  $$ \pi_w \cdot \mathbf{e}_0 = \mathbf{e}_{d(w)} $$
  This equation essentially says "the permutation for sub-cube w must rotate the canonical exit axis ($\mathbf{e}0$) to point along the required direction axis
  ($\mathbf{e}{d(w)}$)". This provides the missing constraint.

  3. Why the Gray Code Appears in the Solution for y_w

  Now, let's see why the formula for $\mathbf{y}_w$ involves a Gray code. We can unroll the recurrence relation:
  $$ \mathbf{y}w = \mathbf{y}{w-1} + \pi_{w-1} \cdot \mathbf{e}_0 = \mathbf{y}{w-1} + \mathbf{e}{d(w-1)} $$
  Starting from $\mathbf{y}_0 = \mathbf{0}$, we get:
  $$ \mathbf{y}w = \sum{k=0}^{w-1} (\pi_k \cdot \mathbf{e}_0) = \sum_{k=0}^{w-1} \mathbf{e}_{d(k)} $$
  This states that the entry point of sub-cube w is the vector sum (XOR sum) of all the direction axes for all preceding sub-cubes.

  This is where the magic happens. This summation has a closed-form solution that is itself a Gray code. Let's look at the "pivot" point you mentioned. It is proven in the
  literature (and is a key part of the formal proof's foundation) that:
  $$ \sum_{k=0}^{w-1} \mathbf{e}_{d(k)} = G\left( \left\lfloor \frac{w}{2} \right\rfloor \right) $$
  This is a non-trivial identity of the direction function `d(k)`.

  So, the class of solutions for the translation is given by the recurrence. When we add the symmetry-based choice for the permutations $\pi_k$, the recurrence unrolls into a
  sum whose closed form is a Gray code.

  Your formula G((w-1) & ~1) is slightly different but relates to a different (but equivalent) formulation where the entry point is defined relative to the exit of the previous
  block. The core insight remains: the translation vector `y_w` is not arbitrarily chosen to be a Gray code; it is the *result* of solving the seam-adjacency recurrence
  relation after the permutations `pi_w` have been fixed by symmetry constraints.

  In the language of $\text{GF}(2)^n$:
   1. The Class of Solutions: Any set of transformations $(S_w)_{w=0}^{2^n-1}$ where $S_w(\mathbf{v}) = \pi_w \cdot \mathbf{v} + \mathbf{y}_w$ that satisfies the recurrence
      $\mathbf{y}_w = \mathbf{y}{w-1} + \pi{w-1} \cdot \mathbf{e}_0$ for all $w>0$ with $\mathbf{y}_0=\mathbf{0}$ will produce a continuous curve.
   2. The Hilbert Curve Choice: We further constrain the solution by choosing permutations $\pi_w$ that orient the curve along the entry/exit axes, i.e., $\pi_w \cdot
      \mathbf{e}0 = \mathbf{e}{d(w)}$.
   3. The Resulting Translation: This specific choice for $\pi_w$ causes the recurrence solution to simplify to $\mathbf{y}_w = G(\lfloor w/2 \rfloor)$. This means the entry
      point for sub-cube w is precisely the origin of sub-cube $\lfloor w/2 \rfloor$. This provides a beautifully symmetric and self-similar structure.

