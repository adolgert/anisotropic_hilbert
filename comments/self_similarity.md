
## Question about Self-Similarity

### Question
I have a question about the anisotropic Hilbert curve. For a regular Hilbert curve, it is self-similar as you change scales. Is this curve also self-similar as you change scales?

### Answer

Not in the *strict* “Hilbert self-similar” sense, unless all side lengths are equal.

For the usual (2^m\times\cdots\times 2^m) Hilbert curve, each refinement step replaces the curve by (2^n) rotated/reflected copies of itself, uniformly scaled by (1/2) in **every** axis (Hamilton describes this recursive copy/rotate/glue construction explicitly in 2D). 

For the anisotropic (unequal-dimension) construction, the refinement rule is **scale-dependent**: at bit-plane/level (i) only the “active” dimensions contribute (those with (m_j>i)). Hamilton’s compact-index formulation makes this explicit via a mask (\mu(i)) defined from which axes are active at iteration (i). 
That means the curve is built from (2^{k(i)}) sub-curves at level (i), where (k(i)=|\mu(i)|) can change with (i). When (k(i)) changes (“activation events”), the subdivision pattern changes, so there is no single fixed similarity rule that repeats at every scale.

What *is* true:

* **Piecewise self-similarity (between activations):** on a range of levels where the active set is constant (so (k(i)) is constant), the refinement behaves like an ordinary (k)-dimensional Hilbert recursion acting only on those axes (copies related by the usual Hilbert rotations/reflections; Hamilton’s (T)-transform is exactly a rotation/reflection on the hypercube labels). 
* **Self-affine overall:** each refinement step scales by (1/2) only along the active axes and leaves inactive axes unchanged at that step. So the natural notion is “self-affine” (anisotropic scaling), not “self-similar” (uniform scaling in all axes).
* **Eventually (fine-scale) Hilbert-like:** once you get below the smallest precision (i.e. for levels (i<\min_j m_j)), *all* axes are active and the refinement is exactly the standard (n)-D Hilbert refinement within those finest fully-active blocks.

So: globally, the anisotropic curve is recursive but **not globally self-similar across all scales**; it is **self-similar on intervals of scales** where the active-axis set doesn’t change, and **self-affine** across the activation transitions.

