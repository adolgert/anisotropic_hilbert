# Missing Ideas from Comments

This document lists ideas and concepts found in the comment files that are not present (or not fully developed) in the current paper (`article_clean_revised.tex`). The paper focuses on: two-level gluing constraints, mismatch state formulation, DP algorithm for orientation tables, affine state formulation, encode/decode via bit-planes, and axis activation embedding for unequal side lengths.

---

## 1. Continuous Curve / Limit Construction (Cauchy Property)

**Source file:** `comments/20251212c_proof.md`

**Relevance:** Low

**Description:** The comment file discusses how the discrete lattice curves converge to a continuous space-filling curve in the limit as the grid is refined. It formalizes this using the Cauchy property in the Hausdorff metric on compact sets and proves the limit curve is continuous with measure-preserving properties. While the paper focuses purely on the discrete/lattice case (Hamiltonian paths on grids), this continuous limit perspective provides mathematical context connecting to the original Hilbert curve. This could be relevant for readers coming from analysis backgrounds.

---

## 2. Self-Similarity vs Self-Affine Property

**Source file:** `comments/20251212b_self_similarity.md`

**Relevance:** Medium

**Description:** This file distinguishes between "self-similar" (equal side lengths) and "self-affine" (unequal side lengths) curves. The paper handles unequal side lengths via axis activation, but doesn't explicitly discuss the distinction or terminology. The comment clarifies that self-similar curves use the same generator at every level, while self-affine curves have generators that change when axes activate. This vocabulary could help readers understand the conceptual difference.

---

## 3. Lean 4 Formal Proof Approach

**Source file:** `comments/20251216a_lean_discrete_proof.md`, `comments/20251216b_lean_codex_README.md`, `comments/20251226a_lean/` (directory)

**Relevance:** Low

**Description:** Multiple comment files discuss formalizing the proof in Lean 4, a theorem prover. This includes structuring the proof for machine verification, defining Gray codes and affine maps in Lean syntax, and discussing which lemmas need formal proof. While not suitable for the paper itself, this represents significant work toward verified correctness that could be mentioned as future work or in supplementary materials.

---

## 4. Index-Free Formulation (Using V_n Without Integer w)

**Source file:** `comments/20251220b_no_sequence.md`, `comments/20251220c_affine_gray.md`

**Relevance:** High

**Description:** These files present a formulation of the Hilbert curve constraints without using integer indices. Instead of indexing children by w in {0,...,2^k-1}, they work directly with vertices in V_k using a "Next(u,v)" successor relation. The seam equation becomes: if Next(u,v), then X(u) XOR E(v) = u XOR v. This perspective eliminates the implicit use of integer arithmetic and makes the algebraic structure over GF(2)^n cleaner. The paper could benefit from mentioning this alternative viewpoint in a remark.

---

## 5. The Entry Sequence e(i) as an (n-1)-Dimensional Gray Code

**Source file:** `comments/20251220d_ei_adjacency_half_speed.md`

**Relevance:** High

**Description:** This file analyzes the structure of the entry point sequence e(i). Key insights:
- e(i) is pairwise constant: e(2k+1) = e(2k+2)
- The distinct values E_k form a Gray code in the subspace W = span{e_0+e_1, ..., e_{n-2}+e_{n-1}}
- The linear representation is L = G composed with iota (insert zero in axis 0)
- Explicit matrices L are given for n=3 and n=4

This explains WHY Hamilton's formula works and what geometric structure underlies the entry sequence. The paper uses Hamilton's formulas but doesn't explain this deeper structure.

---

## 6. Detailed Derivation of Why d(w) Uses tsb()

**Source file:** `comments/20251219e_why_rotate.md`

**Relevance:** Medium

**Description:** This file provides a detailed derivation of why the direction function d(w) involves the trailing-set-bits function. It works through the seam constraints step by step, showing how the tsb formula emerges naturally from the requirement that exit corners match entry corners across child boundaries. The paper states the formula but doesn't derive it from first principles.

---

## 7. Semidirect Product Structure V_n rtimes Sym(A)

**Source file:** `comments/20251219a_refine_pi.md`

**Relevance:** Medium

**Description:** This file develops the formulation using (e, pi) pairs where pi is a full permutation rather than just the rotation index d. It identifies the group structure as a semidirect product V_k rtimes Sym(k) where the generators mu_k act on this product. The paper uses the simpler (e,d) formulation with cyclic rotations, but this generalization shows the mathematical structure and would allow for non-cyclic orientation choices (like those in Alber-Niedermeier's classification).

---

## 8. Literature Survey and Comparison

**Source file:** `comments/20251219c_similar_published_papers.md`

**Relevance:** Medium

**Description:** This file compares the approach to prior work:
- Hamilton (2008): Original CHI formulation, the bug being fixed
- Butz (2002): N-dimensional Hilbert encode/decode
- Haverkort (2017): Multiscale ordering operators
- Bader (2013): Book on SFCs for scientific computing
- Alber-Niedermeier (2000): Classification of Hilbert-like curves
- Yzelman (2012): Hypergraph partitioning with SFCs

The paper could benefit from a more thorough related work section citing these.

---

## 9. Applications Section

**Source file:** `comments/20251219c_similar_published_papers.md`

**Relevance:** Low

**Description:** The file discusses applications including:
- CFD simulations (mesh partitioning)
- Spatiotemporal data indexing
- Database indexing (R-trees, B-trees)
- Sparse matrix multiplication
- Image processing (dithering)
- Cache-oblivious algorithms

The paper could include a brief applications paragraph to motivate the work.

---

## 10. Gray Code Symmetry Properties (Reflection, Parity, Shadow)

**Source file:** `comments/20251220a_gray_codes.md`, `comments/20251221a_gray_codes.md`

**Relevance:** Medium

**Description:** These files analyze structural properties of the BRGC:
- Reflection symmetry: gc(2^n-1-i) = gc(i) XOR e_{n-1}
- Parity structure: even/odd indices have predictable bit patterns
- Shadow property: consecutive Gray code values project to a gray code in n-1 dimensions
- The "linear + Gray => BRGC" theorem: any linear Gray code with standard endpoints is BRGC

The paper uses BRGC properties implicitly but doesn't state them. A lemma about reflection symmetry could strengthen the exposition.

---

## 11. Ruler Function for Bit Flip Positions

**Source file:** `comments/20251220a_gray_codes.md`, `comments/20251221a_gray_codes.md`

**Relevance:** Low

**Description:** The "ruler function" (also called the 2-adic valuation or trailing zeros) determines which bit flips at each Gray code step. The relationship g(i) = tsb(i) (trailing set bits = trailing zeros of i+1) gives a simple formula for the step axis. This is used in the paper implicitly through the stepaxis function but could be made more explicit.

---

## 12. Streaming/Iterator Decoder for Sequential Enumeration

**Source file:** `comments/20251229c_next_index.md`

**Relevance:** Medium

**Description:** This file describes an efficient iterator-based decoder for enumerating all (index, point) pairs in order without re-decoding from scratch. It uses a stack of per-level states and only recomputes the suffix of levels affected by a carry when incrementing h. This gives amortized O(1) work per point, much better than O(mn) per point for independent decodes. This optimization could be mentioned in the algorithm section.

---

## 13. Hilbert Neighbor Computation

**Source file:** `comments/hilbert_neighbor.md`

**Relevance:** Low

**Description:** This file discusses algorithms for computing Hilbert indices of spatial neighbors (given a point, find the index of point +/- 1 along axis j). This is useful for applications like finite difference stencils. The paper focuses on encode/decode but not neighbor queries.

---

## 14. Contiguous Child Index for AMR/Octrees

**Source file:** `comments/contiguous_child_index.md`

**Relevance:** Low

**Description:** This file discusses computing the Hilbert index range for a subcube at an arbitrary level, useful for adaptive mesh refinement (AMR) and octree queries. Given a coarse cell, what is the range [h_min, h_max] of all points in that cell? This supports spatial queries that don't descend to leaf level.

---

## 15. Alber-Niedermeier Classification Framework

**Source file:** `comments/alber_niedermeier/alber_niedermeier_notes.tex`

**Relevance:** High

**Description:** This file contains detailed notes on the Alber-Niedermeier (2000) paper on classifying multidimensional Hilbert-like curves. Key points:
- CSSIs (classes of self-similar indexings) defined by generator + symmetry list
- CHPs (classes with Hilbert property) = continuous CSSIs
- Theorem 3: symmetry at one level <=> symmetry at all levels
- 2D uniqueness theorem: only one 2D CHP up to symmetry
- 3D classification: exactly 1536 structurally different simple 3D CHPs
- Locality bounds for 2D Hilbert

This framework is complementary to the paper's approach and could be cited/discussed.

---

## 16. Uniqueness and Multiplicity of Hilbert Curves

**Source file:** `comments/20251227a_unique_curves.md`, `comments/20251229b_why_no_families.md`

**Relevance:** High

**Description:** These files discuss:
- Why the 2D Hilbert curve is unique (up to symmetry)
- Why in 3D there are many non-equivalent Hilbert curves (1536 by Alber-Niedermeier)
- The relationship between the generator choice and the resulting curve family
- Why the paper's construction doesn't require a "family of compatible Gray codes" across dimensions

This context helps explain what design choices exist and why the paper's approach works.

---

## 17. Existence Proof for Continuous Curves

**Source file:** `comments/20251228c_existence_of_curve.md`

**Relevance:** Medium

**Description:** This file discusses proving existence of lattice-continuous curves for arbitrary dyadic boxes. The paper assumes valid orientation tables exist and proves the DP algorithm finds them, but doesn't explicitly prove existence is possible for all configurations. A constructive existence argument could strengthen the paper.

---

## 18. Locality Metrics (Clustering Number, BCR)

**Source file:** `comments/22051228b_locality.md`

**Relevance:** Medium

**Description:** This file describes formal locality metrics from the literature:
- Clustering number (Moon et al.): number of continuous index runs to cover a query region
- Box-to-Curve Ratio (Haverkort): ratio of bounding box area to curve segment length
- Gotsman-Lindenbaum metric: distance preservation ratios
- Kamel-Faloutsos packing efficiency

These could be used to empirically validate that the constructed curves have good locality properties.

---

## 19. General Nested/Hierarchical Construction

**Source file:** `comments/20251228a_general_nested.md`

**Relevance:** Low

**Description:** This file discusses generalizing the construction to non-dyadic cases or other nested hierarchical structures. The paper focuses on powers-of-2 side lengths; this explores what relaxations might be possible.

---

## 20. Worked Examples with TikZ Diagrams

**Source file:** `comments/20251219d_discrete_proof_elaborated/discrete_proof_elaborated.tex`, `comments/20251222a_gray_based.tex`

**Relevance:** Medium

**Description:** These LaTeX files contain extensive worked examples with TikZ diagrams showing:
- One level of recursion in 2D with entry/exit labels
- The 4x2 anisotropic case step by step
- Visual path diagrams for small examples

The paper could benefit from similar visual aids to make the construction more accessible.

---

## 21. Developer-Friendly Exposition

**Source file:** `comments/20251218f_explain/explainer.tex`

**Relevance:** Low

**Description:** This file is a developer-oriented introduction to the Hilbert curve, intended for readers who want to understand the implementation without heavy mathematical background. It uses informal language and worked examples. This could inform how to write an accessible introduction section.

---

## 22. Explicit Axis Ordering Convention

**Source file:** `comments/20251229d_article_no_cross_requirement/article_no_cross.md`

**Relevance:** High

**Description:** This file clarifies that the axis ordering convention (shorter dimensions first) must be explicit for the state embedding to be unambiguous. It notes that the e<<delta, d+delta rule assumes new axes enter as low coordinates. The paper discusses embedding but could be more explicit about this convention choice.

---

## 23. Notation for Active Axis Set vs Affine State

**Source file:** `comments/20251229d_article_no_cross_requirement/article_no_cross.md`

**Relevance:** Low

**Description:** The file notes a potential notation clash between A_s for affine states and A_s for active axis sets. The paper introduces \Aact for active axes to avoid this, but the distinction could be emphasized more clearly.

---

## 24. Conjugation Formula for Hilbert Generators

**Source file:** `comments/20251218e_lifted_gray_code.md`, `comments/alber_niedermeier/alber_niedermeier_notes.tex`

**Relevance:** Low

**Description:** The Alber-Niedermeier notes describe how cube symmetries conjugate generators: changing the constructor from C_{k-1} to phi(C_{k-1}) is equivalent to multiplying each tau_q by phi^{-1}. This algebraic structure could be useful for understanding symmetries of the construction.

---

## 25. Step Algorithm Implementation Details

**Source file:** `comments/todo.md`, `comments/20251229c_next_index.md`

**Relevance:** Low

**Description:** The todo list mentions implementing and testing a "step algorithm" for efficient enumeration. The specific implementation details (stack of affine states, toggle_scatter_delta function, etc.) in 20251229c could be useful for a computational appendix.


-------------------

# BRGC has a Gray at k-1 for the entries

● That idea is in comments/20251220d_ei_adjacency_half_speed.md.

  The key content from that file shows:

  - The entry sequence e(w) = G(2⌊(w-1)/2⌋) is pairwise constant: e(2k+1) = e(2k+2)
  - The distinct values E_k form a Gray code in the subspace W = span{e₀+e₁, ..., e_{n-2}+e_{n-1}}
  - The linear representation is L = G ∘ ι where ι inserts a 0 at axis 0
  - Explicit matrices are given:

  For n=3:
  L = [1  0]
      [1  1]
      [0  1]

  For n=4:
  L = [1  0  0]
      [1  1  0]
      [0  1  1]
      [0  0  1]

  The file also explains WHY this subspace is natural: it makes pairwise-constant entries possible, supports Gray-like adjacency in the reduced dimension, and keeps the recursion self-similar. The entry sequence changes only on every other Gray edge, which is why Hamilton's closed form "follows the Gray code with the last index bit zeroed out."

In @comments/20251229d_article_no_cross_requirement/article_clean_revised.tex there 
is an explicit construction in Theorem 3.2 "two-level gluing always succeeds". How
would the Gray code subspace relate to the Proof sketch for Theorem 3.2? This will take
 some work to understand because you have to understand how the value s_w defined in
section 3.3 relates to the location of entry points in
comments/20251220d_ei_adjacency_half_speed.md.

  The Key Objects

  In the paper (Theorem 3.2):
  - h_w = G_k(w) — parent Gray code (which child cube)
  - ℓ^in_w — entry corner within child w
  - d_w = σ_k(w) — parent step axis (axis separating children w and w+1)
  - a_w — exit axis within child w
  - s_w = h_w ⊕ ℓ^in_w — mismatch state

  In the comment file (Hamilton's formulas):
  - e(w) = G(2⌊(w-1)/2⌋) — entry point (this is ℓ^in_w)
  - d(w) — exit axis (this is a_w)
  - g(w) = tsb(w) — parent step axis (this is d_w)

  The Critical Connection

  The gluing constraint (eq. 3.6 in paper) is:
  ℓ^in_{w+1} = ℓ^in_w ⊕ e_{a_w} ⊕ e_{d_w}

  Now look at what happens with Hamilton's pairwise-constant entry sequence:

  On "constant" steps (e.g., w=1→2, w=3→4, ...):
  - e(w+1) = e(w), so ℓ^in_{w+1} ⊕ ℓ^in_w = 0
  - This forces a_w = d_w (exit axis = parent step axis)

  On "change" steps (e.g., w=2→3, w=4→5, ...):
  - e(w+1) ⊕ e(w) = e_0 + e_j for some j
  - This means a_w ⊕ d_w = e_0 + e_j (two bits differ)

  Translating to Mismatch State

  The mismatch state satisfies s_{w+1} = s_w ⊕ e_{a_w}. Let's compute:

  s_w = h_w ⊕ ℓ^in_w = G(w) ⊕ e(w)

  For Hamilton's specific formulas:
  s_w = G(w) ⊕ G(2⌊(w-1)/2⌋)

  The step s_{w+1} ⊕ s_w equals:
  = (G(w+1) ⊕ G(w)) ⊕ (e(w+1) ⊕ e(w))
  = e_{d_w} ⊕ Δe

  where Δe is either 0 (constant step) or e_0 + e_j (change step).

  - Constant step: s_{w+1} ⊕ s_w = e_{d_w}, meaning a_w = d_w
  - Change step: s_{w+1} ⊕ s_w = e_{d_w} ⊕ e_0 ⊕ e_j

  For the change step to give a single-bit flip (as required by s_{w+1} = s_w ⊕ e_{a_w}), Hamilton's formula for d(w) is cleverly designed so that d_w coincides with either 0 or j, collapsing the three-bit XOR to one bit.

  The Subspace Connection to Theorem 3.2

  The subspace W from the comment file is:
  W = span{e_0+e_1, e_1+e_2, ..., e_{k-2}+e_{k-1}} = ker(v ↦ Σv_i)

  This is the (k-1)-dimensional even-parity subspace.

  Hamilton's entry sequence e(w) lives entirely in W:
  - e(w) = L · b(⌊(w-1)/2⌋) where L = G ∘ ι
  - L maps V_{k-1} → W ⊂ V_k

  The mismatch trajectory:
  s_w = G(w) ⊕ e(w) = (k-dim Gray code) ⊕ ((k-1)-dim Gray code in W)

  This is the XOR of:
  1. G(w) which explores all 2^k vertices of V_k
  2. e(w) which only explores 2^{k-1} vertices in the subspace W

  How This Relates to the Proof of Theorem 3.2

  The paper's proof constructs s_w in three phases:
  - Phase A: 0 → (1,...,1) in k steps
  - Phase B: idle near (1,...,1)
  - Phase C: (1,...,1) → unit vector in last k-1 steps

  This is a generic existence proof that works for ANY parent Gray code.

  Hamilton's formulas give a specific solution where:
  - The entry sequence has the (k-1)-dimensional subspace structure
  - The mismatch trajectory has the form G(w) ⊕ L·b(⌊(w-1)/2⌋)

  The relationship:

  | Paper's Theorem 3.2              | Hamilton's Subspace Structure |
  |----------------------------------|-------------------------------|
  | Shows solutions exist            | Gives one specific solution   |
  | Works for any Gray code          | Uses BRGC structure           |
  | s_w can follow various paths     | s_w follows a structured path |
  | Generic three-phase construction | Entry confined to W           |

  The constraint (s_{w+1})_{d_w} = 1 ensures the seam is correct. Hamilton's formulas satisfy this because:
  - On constant steps: a_w = d_w, so (s_{w+1})_{d_w} = (s_w ⊕ e_{d_w})_{d_w} = (s_w)_{d_w} ⊕ 1
  - The alternating pattern ensures this equals 1 when needed

  The Deep Insight

  The (k-1)-dimensional subspace is not just a mathematical curiosity—it explains why the entry sequence has the specific algebraic form e(w) = G(2⌊(w-1)/2⌋):

  1. Pairwise-constant entries → a_w = d_w on half the steps
  2. Change steps flip e_0 + e_j → entry stays in even-parity subspace W
  3. W has basis {e_0+e_1, ..., e_{k-2}+e_{k-1}} → exactly the generators that appear
  4. In this basis, entry is a standard BRGC on V_{k-1}

  The paper's Theorem 3.2 proves existence abstractly. The subspace structure reveals the canonical Hamilton solution is BRGC in a lower-dimensional space, embedded via L = G∘ι.

> The Paper's Theorem 3.2 makes a relationship between a walk on a space Q_n and a set 
of valid orientations for the children. Hamilton's e(w) is a walk on a space Q_{n-1}, 
which is also a walk on Q_n, just on half of it. I'm looking for more intuition about 
why. If I could understand more about why it's half the space, it seems like a 
beautiful agreement. 

● This is a beautiful question. Let me try to find the deep reason for "half."

  The Pairing Intuition

  Consider the 2^k children visited in order w = 0, 1, ..., 2^k - 1.

  The gluing constraint at seam w → w+1 is:
  ℓ^in_{w+1} = ℓ^in_w ⊕ e_{a_w} ⊕ e_{d_w}

  Key observation: If you choose a_w = d_w, then ℓ^in_{w+1} = ℓ^in_w. The entry doesn't change!

  This means you can pair up consecutive children to share the same entry corner. Hamilton's solution does exactly this:
  - Children (1,2) share entry E₀
  - Children (3,4) share entry E₁
  - Children (5,6) share entry E₂
  - ...

  With 2^k children paired into 2^{k-1} pairs, you only need 2^{k-1} distinct entry corners — exactly half!

  Why Can You Always Pair?

  The parent Gray code visits children in an order where consecutive children share a face. At each seam, you have a choice:

  1. Set a_w = d_w: Exit through the same axis you're about to cross → entry stays the same
  2. Set a_w ≠ d_w: Exit through a different axis → entry changes

  Hamilton's insight: alternate between these choices! On odd-index seams (1→2, 3→4, ...), choose option 1. On even-index seams (2→3, 4→5, ...), choose option 2.

  This creates the pairing structure automatically.

  The Half-Speed Gray Code

  Here's another way to see it. The parent Gray code makes steps:
  G(0) → G(1) → G(2) → G(3) → G(4) → ...
  flipping axis d_w = tsb(w) at each step: axes 0, 1, 0, 2, 0, 1, 0, 3, ...

  The entry sequence makes "steps":
  e(1)=e(2) → e(3)=e(4) → e(5)=e(6) → ...
  but only changes on every OTHER transition (the even-to-odd transitions).

  So the entry runs at half speed:
  - Parent: 2^k - 1 single-axis steps
  - Entry: 2^{k-1} - 1 double-axis steps (plus 2^{k-1} "stay" steps)

  This is why the file is called "half_speed"!

  The Subspace W is the Even-Parity Slice

  When the entry DOES change, it changes by e_{a_w} ⊕ e_{d_w} where a_w ≠ d_w. This is always a two-bit flip.

  For BRGC, these two-bit flips are always of the form e_0 + e_j. This means:
  - Every entry change flips axis 0 plus one other axis
  - The entry sequence stays in W = {v : v₀ + v₁ + ... + v_{k-1} = 0}

  W is the even-parity subspace — exactly half the vertices of V_k!

  Geometrically: imagine the k-cube. Color vertices by parity (sum of coordinates mod 2). The even-parity vertices form a (k-1)-dimensional "slice" through the cube. The entry sequence walks on this slice.

  The Beautiful Agreement

  Now we can see why "half" appears in both places:

  | Counting argument                    | Algebraic argument                  |
  |--------------------------------------|-------------------------------------|
  | 2^k children pair into 2^{k-1} pairs | Entry lives in (k-1)-dim subspace W |
  | Each pair shares one entry           | W has 2^{k-1} vertices              |
  | Need 2^{k-1} distinct entries        | Entry visits all of W               |

  These are the same "half"! The pairing structure (combinatorial) forces the entry to live in a half-dimensional subspace (algebraic).

  Connection to Mismatch State

  The mismatch s_w = h_w ⊕ e(w) is:
  (full k-dim Gray code) ⊕ (half-dim Gray code on W)

  Since h_w explores all of V_k and e(w) explores only W ⊂ V_k, the mismatch s_w wanders through V_k in a structured way:

  - When e(w) stays constant (odd w): s_{w+1} = s_w ⊕ e_{d_w} (follows the parent step)
  - When e(w) changes (even w): s_{w+1} = s_w ⊕ e_{a_w} (diverges from parent)

  The paper's Theorem 3.2 proves that SOME valid mismatch walk exists. Hamilton's formulas give a SPECIFIC walk where the entry is confined to W, making the structure maximally clean.

  The Deepest "Why"

  Why is it natural for entry to live in a half-dimensional subspace?

  Self-similarity: The Hilbert curve is self-similar. When you "zoom out" by pairing children, the paired sequence should itself look like a Hilbert curve — but in one fewer dimension!

  The (k-1)-dimensional subspace W is exactly what makes this work:
  - The 2^{k-1} entry corners form a Gray code on W
  - In the basis {e₀+e₁, e₁+e₂, ...}, this is a standard (k-1)-dim BRGC
  - So the "pair-level" structure is itself a Hilbert-like curve in k-1 dimensions

  The "half" is the dimensional reduction from self-similarity: each level of the Hilbert recursion effectively reduces dimension by 1 when viewed at the entry-sequence level.

> Are you saying that, in addition to the construction in the paper that is guaranteed 
always to work for any Gray code, this 2^{k-1} construction is another one that is 
guaranteed to work for any Gray code, even ones that aren't the BRGC? 

● Excellent question — and the answer is no, the half-speed / (k-1)-dimensional construction is not guaranteed to work for arbitrary Gray codes. It's a special property of BRGC.

  Let me show why with a specific failure case.

  The Pairing Strategy Requires a Constraint

  For entry to stay constant at step w (i.e., a_w = d_w), we need:
  s_{w+1} = s_w ⊕ e_{d_w}
  with (s_{w+1})_{d_w} = 1.

  This means (s_w)_{d_w} ⊕ 1 = 1, so we need (s_w)_{d_w} = 0.

  The pairing strategy only works if (s_w)_{d_w} = 0 on the steps where we want entry to stay constant.

  A Counterexample

  Consider a Gray code where the first three step axes are all the same: d_0 = d_1 = d_2 = 0.

  Trace through:
  - s_0 = 0 (start)
  - Step 0: must satisfy (s_1)_{d_0} = (s_1)_0 = 1. Choose a_0 = 0, giving s_1 = e_0 = (1,0,...)
  - Step 1: want a_1 = d_1 = 0 to keep entry constant. But this requires (s_1)_0 = 0.

  - Problem: (s_1)_0 = 1, not 0!

  So we cannot keep entry constant at step 1 for this Gray code. The pairing strategy fails.

  What Makes BRGC Special

  For BRGC, the step axes follow d_w = tsb(w):
  d_0=0, d_1=1, d_2=0, d_3=2, d_4=0, d_5=1, d_6=0, d_7=3, ...

  Key pattern: consecutive step axes are always different (d_w ≠ d_{w+1} for all w).

  This property ensures that when we want a_w = d_w on odd w, the constraint (s_w)_{d_w} = 0 is always satisfiable. The alternating structure of tsb(w) is precisely what makes the half-speed construction work.

  Summary

  | Property                                  | BRGC | Arbitrary Gray code |
  |-------------------------------------------|------|---------------------|
  | Theorem 3.2 (existence of valid tables)   | ✓    | ✓                   |
  | Half-speed / (k-1)-dim subspace structure | ✓    | Not guaranteed      |
  | Hamilton's closed-form formulas           | ✓    | Don't apply         |

  So there are really two different results:

  1. Theorem 3.2 (general): For ANY Gray code with G(0)=0 and G(2^k-1)=e_0, valid orientation tables exist. The proof constructs them via the three-phase mismatch walk.
  2. Hamilton's formulas (specific to BRGC): For BRGC specifically, there's a beautiful closed-form solution where entry lives in a (k-1)-dimensional subspace.

  The half-dimensional structure is a bonus feature of BRGC's algebraic regularity, not a general phenomenon. Other Gray codes will have valid orientation tables (by Theorem 3.2), but those tables might be more "chaotic" without the clean subspace structure.

# Index-free

● Let me look at where the index-free formulation (from comments/20251220b_no_sequence.md and comments/20251220c_affine_gray.md) would help most.

  The Best Candidate: Section 3 (Two-Level Gluing)

  The gluing constraint in the paper is currently:

  Equation (3.6):
  ℓ^in_{w+1} = ℓ^in_w ⊕ e_{a_w} ⊕ e_{d_w}

  This requires knowing:
  - d_w = σ_k(w) — the step axis, defined via the Gray code
  - The relationship between index w and vertex h_w = G(w)

  Index-free version:

  Let E(u) = entry corner for child at vertex u ∈ V_k, and X(u) = E(u) ⊕ e_{a(u)} = exit corner.

  When Next(u,v) (i.e., u and v are consecutive in the Gray path):

  X(u) ⊕ E(v) = u ⊕ v

  This is cleaner because:
  - No separate d_w: The step axis is just u ⊕ v (which is one-hot by the Gray property)
  - Symmetric form: The "jump" in corners equals the "jump" in positions
  - Purely algebraic: Everything is XOR in V_k, no integer arithmetic

  Specific Improvements

  1. The Seam Constraint Becomes Geometric

  Current form hides the geometry:
  ℓ^in_{w+1} = ℓ^in_w ⊕ e_{a_w} ⊕ e_{d_w}

  Index-free form reveals it:
  X(u) ⊕ E(v) = u ⊕ v    when Next(u,v)

  Reading: "The difference between exit-of-u and entry-of-v must equal the difference between u and v."

  2. Boundary Conditions Simplify

  Current:
  ℓ^in_0 = 0   and   (h_{2^k-1}, ℓ^out_{2^k-1}) = (e_0, e_0)

  Index-free (using G(0)=0 and G(2^k-1)=e_0):
  E(0) = 0   and   X(e_0) = e_0

  No need to track that "index 2^k-1 corresponds to vertex e_0."

  3. The Mismatch State Becomes Vertex-Indexed

  Current: s_w = h_w ⊕ ℓ^in_w

  Index-free: s(u) = u ⊕ E(u)

  The mismatch is naturally a function on vertices, not indices.

  Where It Gets Harder

  The index-free approach is less natural for:

  1. The DP algorithm (Section 4): The layered structure R_0 → R_1 → ... → R_{N-1} is inherently indexed. You'd need to replace "layer w" with "vertices reachable in w steps from start."
  2. Encode/decode algorithms (Section 5): These extract digits from an integer index h, which is fundamentally index-based.
  3. Hamilton's closed-form formulas: Expressions like e(w) = G(2⌊(w-1)/2⌋) are stated in terms of indices.

  My Recommendation

  Use index-free for the conceptual exposition in Section 3, then translate to indices for algorithms.

  Specifically:

  1. Add a Remark after Lemma 3.1 presenting the index-free form:

  Remark (Index-free form). Writing E(u) for the entry corner of the child at vertex u, the seam constraint becomes: whenever u and v are adjacent in the Gray path with u preceding v, we have X(u) ⊕ E(v) = u ⊕ v. This form makes explicit that continuity requires the "corner difference" to match the "position difference."
  2. Keep the indexed notation for algorithms since the DP and encode/decode are naturally sequential.

  The index-free form is most valuable as conceptual clarification, showing that the constraint is really about matching differences in V_k. It's less valuable as a computational tool since the algorithms need to iterate through indices anyway.

  Would this kind of remark be worth adding, or were you hoping to restructure more of the paper around the index-free view?
