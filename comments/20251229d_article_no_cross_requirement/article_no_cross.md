Key issue (as your `20251229b_why_no_families.md` argues): the paper’s “axis-activation embedding” discussion accidentally conflates two different things:

1. **Level-local seam/gluing constraints** (a statement entirely inside a fixed dimension (k), about (\Gray_k) and ((\mathrm{entry}_k,\mathrm{dir}_k))), versus
2. **How you lift the *orientation state* when new axes become active** (a statement about embedding an affine state from (k) to (k+\delta)).

If those are cleanly separated, the “embedding-compatible Gray-code family” condition can’t sneak in, because the construction and the proof never compare (\Gray_k) to (\Gray_{k'}) for (k\neq k').

I implemented that separation directly in a revised LaTeX version of your paper.

## What I changed in `article_clean.tex` to make the mistake impossible

### 1) Removed the cross-dimensional Gray-code requirement

I deleted the “Compatible Gray-code families / embedding compatibility” definition and the theorem that tried to preserve gluing by “embedding” tables across dimensions.

Instead, I inserted a new subsection (Section 5.2) whose core point is:

* The **two-level gluing constraint** (\eqref{eq:glue-low}) for dimension (k) depends only on (\Gray_k) (via its step axes (d_w)) and the tables ((\mathrm{entry}_k,\mathrm{dir}_k)).
* Therefore, **no cross-dimensional compatibility condition** is required for correctness when axis activation changes (k_s) with level.

This is formalized as a remark:

* **Remark 5.1 (No cross-dimensional Gray-code constraint)** (label `rem:no-families`)

### 2) Made axis activation explicitly about embedding the *state*, not the Gray code

I replaced the old “Embedding orientation tables” section with:

* **Section 5.3: Embedding the affine state when axes activate**
* **Lemma 5.2: State embedding preserves inherited endpoints** (label `lem:state-embed`)

The lemma states (in a clean block-diagonal way) that when (k) increases to (k+\delta), you extend the affine state by acting as identity on newly activated coordinates. This is the only “embedding” you need for correctness.

To match your implementation note (and your markdown’s point), I also added a remark that spells out the packed-bit representation update explicitly:

[
e' = e \ll \delta,\qquad d' = d + \delta,
]

and notes that this is exactly what the decode-all-stack UpdateState does.

### 3) Fixed the notation clash that contributes to conceptual confusion

Originally, (A_s) was used both for:

* the affine “orientation state” (A_s:\V{n}\to\V{n}) (earlier sections), and
* the active-axis set (A_s\subseteq {0,\dots,n-1}) (Section 5).

That’s a trap.

I introduced a separate macro `\Aact` and rewrote the axis-activation part to use:

* (\Aact_s) for the active-axis set/list, and
* (A) (or (A_s) earlier) for affine states.

### 4) Made the “axis order” assumption explicit so state-embedding is unambiguous

Your implementation-style state embedding (bitshift + direction offset) implicitly assumes that when axes activate, they enter as **new low coordinates** in the packed representation.

To make that mathematically explicit and avoid hidden assumptions, I added a concrete choice of axis ordering:

* Choose a permutation (\tau) with **nondecreasing** extents (m_{\tau(0)}\le \cdots \le m_{\tau(n-1)}).
* Then (\Aact_s) is the **suffix** of (\tau) consisting of axes with (m_j\ge s).
* Hence when (k) grows, new axes are prepended, matching the `e<<δ`, `d+δ` rule.

This makes the “embedding step” fully determined and eliminates handwaving about where the new coordinates go.

### 5) Replaced the proof sketch for unequal side lengths with an explicit induction

I rewrote Theorem 5.4 (now still labeled `thm:unequal`) so it no longer says “assume an embedding-compatible family,” and I replaced the “Proof idea” with a concrete induction on recursion level (s) using the truncated domains:

[
\mathbf{m}^{(s)}_j = \min(m_j,s),\qquad \mathcal{D}^{(s)}=\mathcal{D}(\mathbf{m}^{(s)}).
]

The induction step explicitly:

* decomposes (\mathcal{D}^{(s)}) into (2^{k_s}) children,
* uses the induction hypothesis inside each child, and
* uses the **two-level gluing constraint** (\eqref{eq:glue-low}) (for the current (k_s) only) to prove seam adjacency between consecutive children.

No place in the proof compares (\Gray_{k_s}) to (\Gray_{k_{s-1}}), so the original mistaken inference can’t reappear.

## Files produced

* [Download revised LaTeX: `article_clean_revised.tex`](sandbox:/mnt/data/article_clean_revised.tex)
* [Download compiled PDF: `article_clean_revised.pdf`](sandbox:/mnt/data/article_clean_revised.pdf)
* [Download patch (diff): `article_clean_revised.patch`](sandbox:/mnt/data/article_clean_revised.patch)

## How this answers your “what kind of induction?” question

What makes the argument “too clear to make the mistake” is exactly the structure now in Theorem `thm:unequal`:

* The induction is **level-by-level on (s)** (bit significance / recursion depth), not an implicit “it works because Hilbert curves work.”
* The seam argument at each level is **purely (k_s)-dimensional** (it uses only (\Gray_{k_s}) and the (k_s) tables).
* Axis activation is handled by a separate lemma about **state embedding** (block-diagonal extension), so it cannot be conflated with “embedding Gray codes.”

If you want to tighten it even further (optional next refinement), the next step would be to explicitly introduce a “recursive curve constructor” definition (a function that returns a path as a concatenation of oriented subpaths) and then prove a generic lemma of the form “concatenation + seam adjacency ⇒ global adjacency,” which both the equal and unequal theorems can cite. The revised unequal proof is already effectively doing that, but as a self-contained induction.
