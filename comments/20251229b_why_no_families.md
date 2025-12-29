  Proof that Definition 5.1 (Embedding Compatibility) is Unnecessary

  The Claim in article_clean.tex

  Definition 5.1 states that a family {G_k} is embedding-compatible if for every k < k' there exists an injection j: V_k → V_{k'} (inserting zeros in new coordinates) such that:

  $$j(G_k(w)) = G_{k'}(w) \quad \text{for all } w \in 0, \ldots, 2^k - 1$$

  This requires that the first 2^k vertices of G_{k'} must exactly equal the k-dimensional Gray code embedded with zeros in the new coordinates.

  Evidence from the Code

  Observation 1: The tables in random_tables.h use different, unrelated Gray codes at each dimension:

  HILBERT_GRAY_2[4] = {0, 2, 3, 1}     // vertices: 00→10→11→01
  HILBERT_GRAY_3[8] = {0, 2, 6, 4, 5, 7, 3, 1}  // vertices: 000→010→110→100→101→111→011→001

  These are NOT embedding-compatible. To see this, check the first four entries of G_3:
  - G_3(0) = 0 = 000₂ ✓ (matches embed(G_2(0)) = embed(0) = 000)
  - G_3(1) = 2 = 010₂ ✓ (matches embed(G_2(1)) = embed(2) = 010)
  - G_3(2) = 6 = 110₂ ✗ (should be embed(G_2(2)) = embed(3) = 011)
  - G_3(3) = 4 = 100₂ ✗ (should be embed(G_2(3)) = embed(1) = 001)

  Observation 2: The table generator (generate_hilbert_tables.cpp, lines 506-514) generates Gray codes independently for each dimension k:

  for (int k = 1; k <= 7; k++) {
      auto gray = graygen::gray_code(k, gray_type, seed);
      Tables t = build_tables(k, gray, /*force_nonstandard=*/true);
      ...
  }

  There is no cross-dimensional constraint enforced.

  Observation 3: The embedding in hilbert_general.c (lines 259-264) transforms state as:
  if (k > parent_k) {
      int k_shift = k - parent_k;
      st.e <<= k_shift;   // Insert zeros in LOW positions
      st.d += k_shift;    // Offset direction index
  }

  This transformation preserves the parent's entry/exit constraints but does NOT depend on any relationship between the Gray codes.

  ---
  The Correct Theorem

  Theorem (Unnecessary Embedding Compatibility):
  Let {G_k}_{k=1}^{n} be ANY family of Gray codes, where each G_k satisfies:
  - G_k(0) = 0 (starts at origin)
  - G_k(2^k - 1) = e_0 (ends at unit vector along axis 0)

  For each k, let (entry_k, dir_k) be orientation tables satisfying the two-level gluing constraint for G_k. Then the recursive encoder/decoder produces a lattice-continuous bijection for any dyadic hyperrectangle D(m).

  Proof:

  We show that the gluing constraints at different levels are independent, making cross-dimensional Gray code compatibility unnecessary.

  Step 1: Decomposition of the recursion

  At each level s with k_s active dimensions, the algorithm:
  1. Uses Gray code G_{k_s} to traverse 2^{k_s} subcubes
  2. Uses orientation tables (entry_{k_s}, dir_{k_s}) to determine child orientations
  3. Transforms the affine state (e, d) for the next level

  Step 2: Independence of gluing constraints

  The gluing constraint at level s (equation 3.10 in article_clean.tex) is:
  $$\ell^{\text{in}}{w+1} = \ell^{\text{in}}w \oplus e{a_w} \oplus e{d_w}$$

  where d_w = σ_{k_s}(w) is the Gray step axis of G_{k_s} at position w.

  Crucially: This constraint involves ONLY:
  - The Gray code G_{k_s} (through d_w)
  - The orientation tables (entry_{k_s}, dir_{k_s}) (through ℓ^{in}_w and a_w)

  It does NOT involve any other Gray code G_{k'} for k' ≠ k_s.

  Step 3: State embedding preserves boundary conditions

  When the active dimension increases from k to k + δ (new axes activate), the state transform:
  $$e' = e \ll \delta, \quad d' = d + \delta$$

  maps the current orientation to a valid orientation in the larger space. Specifically:
  - T_{e', d'}(0) = e' = (e, 0, ..., 0) — entry in high k coordinates with zeros in new low δ coordinates
  - T_{e', d'}(e_0) = e' ⊕ e_{d'} — exit along the original axis (now offset by δ)

  This ensures the subcube at level s-1 inherits correct boundary conditions from level s. The Gray code G_{k+δ} used at level s-1 can be any Gray code satisfying the boundary conditions — it need not be related to G_k.

  Step 4: Inductive correctness

  By induction on levels:
  - Base case (s = m_max): The top-level traversal visits subcubes in order G_{k_{m_max}}(0), ..., G_{k_{m_max}}(2^{k_{m_max}}-1), which is a valid Gray code path, hence lattice-continuous within the top level.
  - Inductive step: If levels s, s+1, ..., m_max are lattice-continuous, then at level s-1:
    - Within each subcube: uses G_{k_{s-1}} and (entry_{k_{s-1}}, dir_{k_{s-1}}), which satisfy the two-level gluing constraint for G_{k_{s-1}}, hence lattice-continuous.
    - Across subcube boundaries: the gluing constraint ensures consecutive entries/exits are adjacent.
    - Across activation boundaries: state embedding preserves the parent-level boundary conditions.

  Therefore the full traversal is lattice-continuous. ∎

  ---
  Why Definition 5.1 is Wrong

  The error in the article is conflating two independent requirements:

  1. Local requirement: At each level, the orientation tables must satisfy the gluing constraint for the Gray code used at that level.
  2. Boundary requirement: When dimensions change, the state embedding must correctly propagate entry/exit corners.

  The article's Definition 5.1 attempts to unify these by requiring the Gray codes themselves to be compatible. But the actual algorithm only needs:
  - Requirement (1): independently solvable for any Gray code (this is Theorem 2.4)
  - Requirement (2): handled by the state embedding formula, which works regardless of the Gray codes

  The embedding-compatibility condition is sufficient but not necessary. The stronger claim that it is necessary (implicitly made by treating it as a definition rather than a sufficient condition) is false.
  