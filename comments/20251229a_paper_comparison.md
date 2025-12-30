# Comparison of Papers to article_clean.tex

Criteria for comparison against `article_clean.tex`:
1. **Gray→Hilbert**: Proof that any Gray code can define a Hilbert curve
2. **Fast Search**: Fast search method to find paths defining a Hilbert curve given a Gray code
3. **2→Multi Level**: Proof that defining a 2-level Hilbert curve extends to multiple levels
4. **Lattice-Continuous**: Theorem/lemma supporting lattice-continuous Hilbert indices

Key theorems in article_clean.tex:
- Theorem 2.4: Two-level gluing always succeeds (for any Gray code with fixed endpoints)
- Lemma 2.3: Mismatch-state form of gluing constraints
- Algorithm 2: DP to compute orientation tables in F_2^k
- Theorem 4.2: Embedding preserves gluing
- Theorem 4.3: Correctness for unequal side lengths

---

## Hamilton - Technical Report CS-2006-07 (32 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | FULL | Theorems 2.1, 2.9, 2.10 |
| Fast Search | PARTIAL | Theorem 3.2 + Algorithms 4-5 (O(n) ranking with bit masks) |
| 2→Multi Level | FULL | Theorem 2.9 and equation (1) prove recursive construction |
| Lattice-Continuous | FULL | Section 3, Theorem 3.2 |

Relevant theorems:
- **Theorem 2.1** (p.7): Closed-form Binary Reflected Gray Code
- **Theorem 2.2** (p.8): Binary Reflected Gray Code Inverse
- **Lemma 2.3** (p.8): Dimension of Change in the Gray Code
- **Lemma 2.4** (p.9): Symmetry of the Gray Code
- **Theorem 2.9** (p.12): Intra Sub-hypercube Directions
- **Theorem 2.10** (p.13): Entry Points
- **Theorem 3.2** (p.22): Gray Code Rank

---

## Hamilton & Rau-Chaplin 2008 - Compact Hilbert Indices (9 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | FULL | Algorithm 1 uses Gray code inverse for Hilbert index |
| Fast Search | FULL | Theorem 3.5 + Algorithm 3 (GrayCodeRank) O(n) |
| 2→Multi Level | FULL | Algorithm 1 shows recursive composition |
| Lattice-Continuous | FULL | Section 3.1, Theorem 3.5 |

Relevant theorems:
- **Lemma 3.2** (p.5): Gray code bit relationship
- **Lemma 3.3** (p.5): Gray code inversion
- **Lemma 3.4** (p.5): Principal Bits
- **Theorem 3.5** (p.6): Gray Code Rank

---

## Alber & Niedermeier 2000 - Multidimensional Curves with Hilbert Property (18 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | PARTIAL | Section 2.1 discusses Hamiltonian circuits but focuses on permutation-based description |
| Fast Search | NO | Not addressed |
| 2→Multi Level | FULL | **Theorem 3 (p.9)** explicitly proves this |
| Lattice-Continuous | PARTIAL | Definition 1, Remark 5 discuss continuity constraints |

Relevant theorems:
- **Definition 1** (p.5): Constructor Relation - formal definition of recursive 2-level construction
- **Definition 2** (p.5): Class of Self-Similar Indexings (CSSI)
- **Theorem 3** (p.9): If two CSSIs differ at one level by symmetry, they differ at all levels the same way
- **Theorem 4** (p.10): 2D Uniqueness - classical 2D Hilbert curve is unique modulo symmetry
- **Theorem 6** (p.11): 3D Classification - exactly 1536 structurally different simple 3D Hilbert curves
- **Theorem 7** (p.14): Locality Bounds for 2D

ajd: The definitions about indexings that form Hilbert curves are pretty loose. They assume it's the same curve at each level. He's making it quite consistent to use the same indexing and same rotations at every level.

---

## Haverkort - Sixteen Space-Filling Curves (28 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | PARTIAL | Pages 5-6 discuss Gray code base pattern G2(d), but not proof for ANY Gray code |
| Fast Search | NO | Section 9 is for traversal generation, not Gray code search |
| 2→Multi Level | FULL | Section 2 notation system, recursive structure implicit throughout |
| Lattice-Continuous | PARTIAL | Pages 13-15, face-continuity properties |

ajd: Very quick take.

---

## Haverkort - Recursive Tilings (28 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | NO | Focuses on Arrwwid number, not Gray codes |
| Fast Search | NO | Not addressed |
| 2→Multi Level | PARTIAL | Pages 5-9, Theorems 1-3 on recursive tilings |
| Lattice-Continuous | FULL | **Theorem 4** (p.14), **Theorem 5** (p.17) on Arrwwid bounds |

Relevant theorems:
- **Theorem 4** (p.14): Dekking's curve achieves optimal Arrwwid number three
- **Theorem 5** (p.17): Space-filling curves based on recursive tilings have Arrwwid ≥ 3
- **Lemma 3** (p.23): Relationship between angle and turn at vertices
- **Lemma 4** (p.23): Bounds on vertex-tile incidences

---

## Haverkort - Inventory of 3D Hilbert (27 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | NO | Uses Alber-Niedermeier framework, not Gray code proof |
| Fast Search | PARTIAL | Section 6, Lemmas 1-6 (pp.20-23) constrain enumeration search space |
| 2→Multi Level | NO | Assumed but not proven |
| Lattice-Continuous | PARTIAL | Property 2.2 (p.4) - vertex-continuity definition |

Relevant content:
- **Lemmas 1-6** (pp.20-23): Necessary conditions on gate locations
- **Property 2.2** (p.4): Vertex-continuity definition

ajd: no

---

## Haverkort - Four-Dimensional Hilbert Curves for R-trees (20 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | NO | Not addressed |
| Fast Search | NO | Section 3.1 is verification, not search |
| 2→Multi Level | NO | Empirically verified but not proven |
| Lattice-Continuous | PARTIAL | Properties 2.1-2.2 (p.5) on continuity |

ajd: no

---

## Haverkort - Hyperorthogonal Well-Folded Hilbert Curves (35 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | PARTIAL | Definition 1 (p.6), Definition 5 (p.9) - uses G(d) but not proof for ANY Gray code |
| Fast Search | FULL | **Theorem 19** (pp.15-16), **Algorithm 1** (pp.25-35) O(d·k) time |
| 2→Multi Level | FULL | **Lemma 24** (p.18), **Theorem 46** (p.23) |
| Lattice-Continuous | PARTIAL | Theorem 13 (p.11), Lemma 12 (p.11), Theorem 7 (p.8) |

Relevant theorems:
- **Definition 1** (p.6): Free curve G(d) using binary reflected Gray code
- **Theorem 7** (p.8): Conditions for face-continuous curves
- **Lemma 12** (p.11): Edge locality bounds
- **Theorem 13** (p.11): Box-to-curve ratio ≤ 4
- **Theorem 19** (pp.15-16): Existence/uniqueness of hyperorthogonal well-folded curves
- **Lemma 24** (p.18): Self-similar extension property
- **Theorem 46** (p.23): Existence for any d ≥ 3

ajd: Haverkort shows that a Hilbert curve exists that is self-similar, hyperorthogonal, well-folded, in d-dimensions. Not for any Gray code.

---

## Haverkort - Locality and Bounding-Box Quality of 2D Curves (17 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | NO | 2D only, no Gray code theory |
| Fast Search | PARTIAL | Section 5.2, Theorem 5 (p.143) - probe-based algorithm |
| 2→Multi Level | NO | 2D only |
| Lattice-Continuous | PARTIAL | Theorem 2 (p.138), Lemma 1 (p.137) on bounding-box quality |

---

## Ningtao Chen 2007 - New Algorithm for Encoding/Decoding Hilbert Order (12 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | NO | Does not discuss Gray codes |
| Fast Search | NO | Not addressed |
| 2→Multi Level | PARTIAL | Pages 899-900 describe replication rules constructively |
| Lattice-Continuous | PARTIAL | Pages 898, 902 discuss bijection problem and variant |

---

## Breinholt & Schierz 1998 - Algorithm 781 (6 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | NO | No Gray code discussion |
| Fast Search | NO | Not addressed |
| 2→Multi Level | PARTIAL | Pages 185-187 describe recursive unit shape construction |
| Lattice-Continuous | NO | Not addressed |

---

## Jia et al. 2025 - Efficient Group-Based Hilbert Encoding (14 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | NO | Not addressed |
| Fast Search | NO | Not addressed |
| 2→Multi Level | PARTIAL | Theorems 1-2 (p.5) support virtual filling for multi-level extension |
| Lattice-Continuous | NO | Not addressed |

Relevant theorems:
- **Theorem 1** (p.5): Initial state computation for first group
- **Theorem 2** (p.5): Virtual filling produces zero code

---

## Jin & Mellor-Crummey 2005 - SFCGen Framework (30 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | NO | Assumes Gray code structure |
| Fast Search | PARTIAL | Section 3.3 (pp.132-133) curve indexing algorithm |
| 2→Multi Level | PARTIAL | Sections 3.1, 4.4 show recursive composition |
| Lattice-Continuous | NO | Not addressed |

---

## Bartholdi & Goldsman 2000 - Vertex-Labeling Algorithms (27 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | NO | No Gray code discussion |
| Fast Search | PARTIAL | O(n) algorithms in Section 2.9 (p.17) |
| 2→Multi Level | FULL | Section 2.2 (p.8) shows iterative multi-level extension |
| Lattice-Continuous | NO | Not addressed |

ajd: Sure. It's a process at least.


---

## Couch, Daniel & McNicholl 2012 - Computing Space-Filling Curves (17 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | NO | Focuses on computable analysis |
| Fast Search | NO | Not addressed |
| 2→Multi Level | NO | Not addressed |
| Lattice-Continuous | NO | General Peano continua theory |

Relevant theorems (for general theory):
- **Theorem 6** (pp.384-385): Effective Hahn-Mazurkiewicz Theorem
- **Theorem 5** (p.383): Effective Aleksandrov-Hausdorff Theorem

This paper is about computable analysis — asking when you can algorithmically construct a space-filling curve onto a given target space. Let me explain the two theorems:

  Theorem 5 (Effective Aleksandrov-Hausdorff)

  Statement: From a "name" (computational description) of a compact set X ⊆ ℝⁿ, we can uniformly compute a surjection from the Cantor set C onto X.

  Meaning: The Cantor set can always be computably mapped onto any compact set. This is the "easy" first step — Cantor sets are simpler than intervals because they're totally disconnected.

  Theorem 6 (Effective Hahn-Mazurkiewicz)

  Statement: From a name of a Peano continuum X ⊆ ℝⁿ and a local connectivity operator for X, we can uniformly compute a surjection g : [0,1] → X.

  Meaning: To compute an actual space-filling curve (from the interval [0,1]), you need two pieces of information:
  1. A description of the target space X
  2. A "local connectivity operator" — algorithmic access to how neighborhoods decompose into connected pieces

  Why this matters for Hilbert curves

  The paper's key negative result (Theorem 1) shows there exists a computable Peano continuum that is not the image of any computable function on [0,1]. This proves the local connectivity operator is genuinely necessary.

  Connection to Alber's formalism: The recursive self-similar structure that Alber captures with generators and permutations is essentially providing the "local connectivity" information algorithmically. The CSSI framework tells you how to decompose the space at each scale — which is precisely what a local connectivity operator does.

  In discrete settings (finite grids), this is less of an issue, but the theory explains why the recursive structure of Hilbert curves isn't just elegant — it's computationally essential.

---

## Franco 2018 - Alternative Patterns of Multidimensional Hilbert Curve (22 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | PARTIAL | Equation (3) p.8425 describes adjacency constraint, no proof for ANY Gray code |
| Fast Search | FULL | **Figure 7** (p.8428) PATTERNLISTING recursive algorithm |
| 2→Multi Level | FULL | Section 3.2, Figure 4 (p.8424), Table 5 (p.8430) |
| Lattice-Continuous | NO | Focuses on locality metrics |

ajd: This one does new patterns by hand.

---

## Franco 2025 - Pareto Multi-Objective Optimization (11 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | PARTIAL | References Franco 2018 constraint formulation |
| Fast Search | FULL | Section 3 (pp.3-5), isometry-free detector O(D + D log D) |
| 2→Multi Level | FULL | Section 2.2 (pp.3-4), Figure 3 (p.4) |
| Lattice-Continuous | NO | Focuses on Pareto optimality |

ajd: A limited search to look for best locality.

---

## Gray Codes and Symmetric Chains - Gregor et al. 2018 (14 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | NO | Hamilton cycles in hypercubes, not Hilbert curves |
| Fast Search | PARTIAL | Lemma 6 (p.7) O(1) lexical matching properties |
| 2→Multi Level | NO | SCDs via products, not Hilbert hierarchies |
| Lattice-Continuous | NO | Not addressed |

Relevant theorems:
- **Theorem 1** (p.2): Middle four levels of (2n+1)-cube have Hamilton cycle
- **Theorem 5** (p.5): SCD extension via products
- **Lemma 6** (p.7): Lexical matching properties

---

## Hamiltonian Cycles and Symmetric Chains in Boolean Lattices - Streib & Trotter 2014 (22 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | PARTIAL | Structural framework for Gray codes via Boolean lattices |
| Fast Search | NO | Constructs paths, no search algorithms |
| 2→Multi Level | FULL | **Theorem 10** (p.1571), **Theorem 6** (p.1567) |
| Lattice-Continuous | PARTIAL | Symmetric chain structure enforces continuity |

Relevant theorems:
- **Theorem 3** (p.1567): B(n) has SCP
- **Theorem 5** (p.1567): B(n) satisfies strong HC-SCP property
- **Theorem 6** (p.1567): HC-SCP preserved under products
- **Theorem 10** (p.1571): Strong HC-SCP preserved under P × 2 product

---

## Hypercube Problems Lecture Notes - Gregor 2021 (14 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | NO | Defines Gray codes but not connection to Hilbert curves |
| Fast Search | PARTIAL | O(1) amortized loopless Gray code generation (p.26-4) |
| 2→Multi Level | FULL | **Theorem 21** (p.26-9), **Theorem 28** (p.26-10) |
| Lattice-Continuous | FULL | **Theorem 28** (p.26-10) SCD extends to Hamilton cycles |

Relevant theorems:
- **Definition 6** (p.26-3): Gray code as Hamiltonian path in Qn
- **Theorem 14** (p.26-7): Monotone Gray code exists for all n
- **Theorem 18** (p.26-8): Middle level graph is Hamiltonian
- **Theorem 21** (p.26-9): Central level graphs are Hamiltonian
- **Proposition 26** (p.26-9): Bn has SCD
- **Theorem 28** (p.26-10): Greene-Kleitman SCD extends to Hamilton cycle

---

## A Group-Theoretic Model for Symmetric Interconnection Networks - Akers & Krishnamurthy 1989 (12 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | NO | Cayley graphs, not Gray codes/Hilbert |
| Fast Search | NO | Routing algorithms, not path search |
| 2→Multi Level | PARTIAL | Theorem 4 Property 5 (p.560) hierarchical decomposition |
| Lattice-Continuous | NO | Not addressed |

---

## A New Approach to the Snake-In-The-Box Problem - Kinny 2012 (6 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | PARTIAL | Discusses Gray codes as transition sequences |
| Fast Search | NO | Monte-Carlo tree search for snakes |
| 2→Multi Level | NO | Not addressed |
| Lattice-Continuous | NO | Not addressed |

---

## Hamilton Cycle in k-Sided Pancake Network - Cameron et al. 2021 (15 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | PARTIAL | Theorem 1 proves cyclic flip Gray code |
| Fast Search | PARTIAL | **Algorithm 1** (p.148) O(n)-time successor |
| 2→Multi Level | PARTIAL | Theorem 1, Equation 1 show recursive definition |
| Lattice-Continuous | NO | Not addressed |

Relevant theorems:
- **Theorem 1** (p.145): Cyclic flip Gray code for colored permutations
- **Lemma 2** (p.145): Flip-sequence for recursive construction
- **Lemma 4** (p.147): Successor rule
- **Algorithm 1** (p.148): O(n) successor computation
- **Lemma 5**: Average flip length bounded by √k·e

---

## On the Metric Properties of Discrete Space-Filling Curves - Gotsman & Lindenbaum 1996 (4 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | NO | Not addressed |
| Fast Search | NO | Not addressed |
| 2→Multi Level | NO | Metric properties only |
| Lattice-Continuous | PARTIAL | **Theorems 3-4** (p.796) locality bounds |

Relevant theorems:
- **Theorem 3** (p.796): L₁(H^m) ≤ (m+3)^(m/2)2^m for m-dimensional Hilbert curve
- **Theorem 4** (p.796): 6(1-O(2^(-k))) ≤ L₁(H²) ≤ 6⅓ for 2D

---

## Alternative Algorithm for Hilbert's Space-Filling Curve - Butz 1971 (3 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | NO | Algorithmic, no proof |
| Fast Search | NO | Generation algorithm only |
| 2→Multi Level | IMPLICIT | In recursive structure |
| Lattice-Continuous | PARTIAL | "Realization of Continuous Mapping" section |

---

## Onion Curve - Xu et al. 2018 (4 pages)

| Criterion | Match | Details |
|-----------|-------|---------|
| Gray→Hilbert | NO | Not addressed |
| Fast Search | NO | Not addressed |
| 2→Multi Level | IMPLICIT | In recursive definition |
| Lattice-Continuous | NO | Not addressed |

Relevant lemma:
- **Lemma 1** (p.1237): No SFC can have constant clustering number over both row and column queries

---

## SKIPPED (>35 pages)

- **analysis of the clustering properties of the hilbert space filling curve.pdf** (36 pages)
- **haverkort harmonious Hilbert.pdf** (40 pages)
- **Padula et al. - The Standard Vector Library...** (46 pages)
- **haverkort how many hilbert curves.pdf** (61 pages)
- **mcnulty geometric searching with space filling curves.pdf** (139 pages)
- **mcnulty geometric searching with spacefiling curves.pdf** (139 pages) - duplicate
- **bader 2012 space filling curves.pdf** (286 pages)

---

## IRRELEVANT (Application papers)

- **Development of a Modified Hilbert Curve Fractal Antenna...** - Antenna design
- **Bai Hilbert-Based Generative Defense...** - Machine learning defense
- **rapid delaunay triangulation...** - Computational geometry
- **semi-resolved CFD-DEM approach...** - Computational fluid dynamics
- **spatiotemporal trajectory data index...** - Database indexing
- **Abdelkader convex approximation and the hilbert geometry.pdf** - Convex geometry (different Hilbert)
- **sparse matrix vector.pdf** - Cache optimization
- **spores-wang.pdf** - Linear algebra optimization
- **gockenbach 1996 hilbert class library.pdf** - Software library (Hilbert spaces, not curves)

---

## Summary: Best Matches for article_clean.tex

### For criterion 1 (Gray→Hilbert proof):
- **Hamilton TR** - FULL MATCH (Theorems 2.1, 2.9, 2.10)
- **Hamilton & Rau-Chaplin 2008** - FULL MATCH (Algorithm 1)

### For criterion 2 (Fast search method):
- **Hamilton & Rau-Chaplin 2008** - FULL MATCH (Theorem 3.5, Algorithm 3)
- **Haverkort Hyperorthogonal** - FULL MATCH (Theorem 19, Algorithm 1)
- **Franco 2018** - FULL MATCH (Figure 7)
- **Franco 2025** - FULL MATCH (Section 3)

### For criterion 3 (2-level extends to multi-level):
- **Alber & Niedermeier 2000** - FULL MATCH (Theorem 3, p.9) - most explicit proof
- **Hamilton TR** - FULL MATCH (Theorem 2.9)
- **Streib & Trotter 2014** - FULL MATCH (Theorems 6, 10)
- **Gregor Lecture Notes** - FULL MATCH (Theorems 21, 28)
- **Haverkort Hyperorthogonal** - FULL MATCH (Lemma 24, Theorem 46)

### For criterion 4 (Lattice-continuous indices):
- **Hamilton TR** - FULL MATCH (Section 3, Theorem 3.2)
- **Hamilton & Rau-Chaplin 2008** - FULL MATCH (Section 3.1, Theorem 3.5)
- **Haverkort Recursive Tilings** - FULL MATCH (Theorems 4, 5)
- **Gregor Lecture Notes** - FULL MATCH (Theorem 28)
