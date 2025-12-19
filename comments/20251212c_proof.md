# Extension to continuous indices

## What it means to “extend to a true continuous curve”

A “true” (topological) Hilbert/Peano-style space-filling curve is a **continuous** map
[
H:[0,1]\to B
]
whose image is the whole target box (B) (i.e., **surjective**). Hamilton’s abstract uses exactly this continuity viewpoint (“continuous self-similar functions which map compact multi-dimensional sets into one-dimensional ones”). 
(Separately: the report’s introduction also contains an “one-to-one” phrase; for a space-filling curve onto a higher-dimensional region that cannot literally be injective. The standard correct requirement is continuity + surjection.)

Your discrete construction already gives the key *finite* property Hamilton emphasizes for Hilbert lattices: **unit lattice steps** (“always take steps of unit length”). 
The continuous curve is obtained by taking a **limit of finer-and-finer dyadic refinements**.

---

## The concrete continuous construction for unequal side lengths

### Step 1: Fix the “unequal side-length type” via dyadic offsets

Let (n\ge 2). Choose a fixed offset vector
[
c=(c_0,\dots,c_{n-1})\in\mathbb{N}^n.
]

This defines the target **dyadic box**
[
B_c=\prod_{j=0}^{n-1} [0,2^{c_j}].
]

(Interpretation: these (c_j) are exactly the “finite number of activation events” that encode unequal dimensions; after those finitely many coarse splits, the refinement becomes “all dimensions active” forever.)

### Step 2: Define the refinement sequence of anisotropic grids

For each depth (k=0,1,2,\dots), define an exponent vector
[
m^{(k)}=(k+c_0,\dots,k+c_{n-1}).
]

So the lattice has side lengths (2^{k+c_j}) along axis (j), and total index bits
[
M_k=\sum_{j=0}^{n-1}(k+c_j)=nk+\sum_j c_j.
]

This is the “two activation events / multiple activation events” situation in the simplest stable way: the **offsets** cause the early unequal behavior; then each additional (k) refines every axis once more.

### Step 3: Use your (fixed) discrete decode at each depth

Let (\mathrm{decode}(\cdot,m^{(k)})) be the lattice-continuous bijection you already implemented (based on Hamilton’s (T)-transform machinery, including the correct inverse (T^{-1}) (Lemma 2.12)  and the Algorithm-2 style state update for ((e,d)) ).

For each (t\in[0,1]), define an index at depth (k):
[
h_k(t)=\left\lfloor t,2^{M_k}\right\rfloor \quad\text{(with the convention }h_k(1)=2^{M_k}-1\text{)}.
]

Let
[
p_k(t)=\mathrm{decode}(h_k(t),m^{(k)})\in\prod_j{0,1,\dots,2^{k+c_j}-1}.
]

Now scale it into (B_c) by
[
H_k(t)=\frac{p_k(t)+\tfrac12\mathbf{1}}{2^k}\in B_c,
]
(where (+\tfrac12) chooses the **center** of the visited dyadic cell; it’s optional but avoids boundary bias).

### Step 4: Define the continuous curve as the limit

Define
[
H(t)=\lim_{k\to\infty} H_k(t).
]

The key work is showing this limit exists for every (t) (except for the usual binary-expansion ambiguity at dyadic rationals, which you handle the standard way by choosing either expansion) and that the resulting (H) is continuous and surjective.

---

## The “next verification step” that makes the proof go through

Everything hinges on a **refinement consistency lemma**:

### Lemma A: Bit-refinement consistency

For fixed offsets (c), for “generic” (t) (i.e., excluding the measure-zero set of boundary (t) that land exactly on dyadic interval endpoints at some depth),
[
p_{k+1}(t)\ \text{right-shifted by 1 bit in every coordinate equals}\ p_k(t),
]
i.e.
[
p_{k+1}(t)\gg 1 = p_k(t)\quad\text{(componentwise)}.
]

Intuition: (h_{k+1}(t)) is literally the binary expansion of (t) truncated to (M_{k+1}) bits, and its first (M_k) bits equal (h_k(t)). The decode algorithm reconstructs coordinate bits level-by-level (Hamilton’s inversion structure: extract bits, apply (T^{-1}), write coordinate bits, update ((e,d))). 
So the higher coordinate bits are determined by the higher index bits; adding one more refinement level only appends new least-significant coordinate bits.

This is exactly the “nested dyadic cells” property you need for a continuous limit.

### Lemma B: Cauchy property (hence existence of the limit)

From Lemma A,
[
H_{k+1}(t)=H_k(t)+\frac{\delta_k(t)}{2^{k+1}}
]
where (\delta_k(t)\in{0,1}^n). Hence
[
|H_{k+1}(t)-H_k(t)|*\infty \le 2^{-(k+1)}.
]
So ((H_k(t))*{k\ge0}) is Cauchy for each (t), therefore converges.

### Lemma C: Continuity

If two parameters (t,t') share the first (M_k) bits of their binary expansions, then (h_k(t)=h_k(t')) and hence (p_k(t)=p_k(t')), so (H(t)) and (H(t')) lie in the same depth-(k) cell of diameter (O(2^{-k})). This implies uniform continuity of (H).

### Lemma D: Surjectivity (“space-filling”)

Given any (x\in B_c), choose its binary expansion in each coordinate (avoiding the all-1s / all-0s ambiguity in the standard way). Those coordinate bits determine a consistent sequence of dyadic subcells. At each level, because the local mapping is bijective (Hamilton’s (T) is bijective  and preserves Gray adjacency , and the HilbertIndex/HilbertIndexInverse steps are reversible ), there is a unique digit (w) selecting the correct subcell. Concatenating these digits gives a parameter (t) with (H(t)=x).

---

## Code: yes, and it’s already packaged

I added a small continuous wrapper around your discrete `encode/decode`:

* `continuous_anisotropic_hilbert.py`

  * `eval_point(t, offsets, depth, ...)`: evaluate the depth-(k) approximation (H_k(t))
  * `approx_inverse(x, offsets, depth, ...)`: return the depth-(k) parameter interval ([h/2^{M_k},(h+1)/2^{M_k})) containing (x)
  * `refinement_consistency_holds(...)`: checks the key lemma (p_{k+1}\gg 1=p_k)

* `test_continuous_anisotropic_hilbert.py`

  * tests the refinement lemma on many random (t)
  * tests scaled lattice continuity at fixed depth (step length (2^{-k}))
  * tests finite-depth inverse consistency

Download:

* [anisotropic_hilbert_continuous_package.zip](sandbox:/mnt/data/anisotropic_hilbert_continuous_package.zip)
* [continuous_anisotropic_hilbert.py](sandbox:/mnt/data/continuous_anisotropic_hilbert.py)
* [test_continuous_anisotropic_hilbert.py](sandbox:/mnt/data/test_continuous_anisotropic_hilbert.py)
* [demo_continuous.py](sandbox:/mnt/data/demo_continuous.py)

How to run:

```bash
cd /mnt/data
python -m unittest -v
python demo_continuous.py
```

---

## What this gives you (and what it doesn’t)

* Gives: a **mathematically standard** continuous space-filling curve (H:[0,1]\to B_c) for **unequal dyadic side lengths** (2^{c_j}), built as the uniform-refinement limit of your lattice-continuous anisotropic Hilbert orderings.
* Gives: clean “activation-event” interpretation: offsets (c) produce finitely many coarse unequal activation levels; after that, refinement is uniform.
* Doesn’t give (automatically): a canonical choice for non-dyadic side-length ratios without applying a final affine scaling. But affine scaling preserves continuity and surjectivity, so if you want a physical box (\prod[0,L_j]), you can set `lengths=(L0,...,Ln-1)` and get an exactly-filled target box by composition.

If you want the next proof step written as a formal theorem/lemma chain in Hamilton’s style, the natural order is:

1. state the refinement-consistency lemma (p_{k+1}\gg 1=p_k) precisely,
2. prove it by aligning the bit-prefix property of (h_k(t)) with the level-by-level structure of HilbertIndexInverse , plus the correctness of (T^{-1}) ,
3. conclude existence/continuity/surjectivity of (H) by nested-cell arguments.

That proof is now “mechanical” given the lemma—and the new tests are specifically checking that lemma in the most sensitive small cases.

