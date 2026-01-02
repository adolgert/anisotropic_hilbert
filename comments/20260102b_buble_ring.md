## What “Bubble” and “Ring” are in Bradley

In Bradley & Jahn, **Bubble** and **Ring** are **coordinate-order permutation strategies** used in their `PERMUTATE()` step: given a distinguished coordinate index (d), they update the ordered list of coordinate identifiers (D) by moving (d) to the front in one of two “orderly” ways:

* **Bubble (“pull”)**: move (d) to the front, keeping the relative order of the other coordinates (a *move-to-front* operation).
* **Ring (“jump”)**: treat (D) as cyclic and *rotate* so that (d) becomes the first coordinate (a *cyclic rotation* operation).

So: Bubble and Ring are **not** Gray codes; they are **policies for updating a coordinate permutation/order** while walking/refining a Hilbert family.

## Do Bubble and Ring apply only to BRGC, or to any Gray code?

### What the Bradley paper itself assumes

Bradley’s construction and algorithms are written around the **p-adic reflected Gray code** (binary case (p=2) corresponds to the BRGC). In that sense, the paper *uses* Bubble/Ring in the BRGC/reflected-Gray setting.

### What Bubble/Ring *conceptually* need

Bubble/Ring themselves only need:

1. a dimension set ({0,\dots,k-1}), and
2. a distinguished axis index (d\in{0,\dots,k-1}) at each step,

to update an ordering (D).

They do **not** require any special BRGC property like the “ruler function” / trailing-zeros formula. So they can be paired with **any Gray code on the hypercube** (i.e., any sequence ((h_w)) with one-bit steps), because any such Gray code provides a step axis
[
h_{w+1} = h_w \vplus \mathbf e_{d_w},\quad\text{so }d_w\text{ exists and is unique.}
]

**Bottom line:** Bubble and Ring are *not* BRGC-specific ideas. Bradley *instantiates* them with the reflected code, but the permutation rules can be used with **any** Gray code (binary or “coordinate-adjacent” in general).

## Can Bubble/Ring be generalized beyond BRGC?

Yes—there are two layers:

1. **Generalize to any Gray code**: replace “(d)” with the Gray-code step axis (d_w) computed from your chosen code.
2. **Generalize to your article’s setting** (including unequal side lengths / active-axis sets): apply the same update rules on the **current active axis list** at that level.

Ring generalizes trivially (it’s a rotation). Bubble generalizes as a standard move-to-front list update.

## Is your intended use in `article.tex` appropriate?

Mostly yes, with one important clarification:

* In `article.tex`, the mismatch recurrence is already
  [
  s_{w+1} = s_w \vplus \mathbf e_{a_w},
  ]
  and the seam constraint is
  [
  (s_{w+1})_{d_w}=1.
  ]
  That means:

  * if ((s_w)_{d_w}=0), then you are **forced** to choose (a_w=d_w);
  * if ((s_w)_{d_w}=1), then you have a **choice**: any (a_w\neq d_w) works.

So Bubble/Ring should be used as a **tie-breaker policy** for the “free choice” case ((s_w)_{d_w}=1): they give you a structured, incremental way to pick *which* non-(d_w) bit to flip.

### One more nuance (important if you care about matching Bradley exactly)

* Your current exposition uses **cyclic** transforms (T_{e,d}(y)=\rho^d y \vplus e).
  That aligns naturally with **Ring** (cyclic rotation).
* **Bubble** is generally **not** representable as a pure cyclic rotation (\rho^d) when (k>2); it corresponds to a more general coordinate permutation.

  * If you want Bubble “as Bradley defines it”, you should frame it in `article.tex` under your **general affine automorphisms** (A(x)=Px\vplus a) (with arbitrary permutation matrices (P)), not only the cyclic subgroup.

If your goal is simply “a good incremental mismatch policy,” you can still use Bubble as a policy for choosing (a_w), but be aware it’s conceptually outside the “cyclic-only” restriction.

## A Bubble/Ring mismatch-update algorithm for any Gray code

You asked for an update rule that produces (s_{w+1}) from (s_w) (incrementally) without needing a table indexed by (w). The clean way is:

* you use the Gray code only through its **step axis** (d_w),
* and you maintain a small cached state (D_w) (a permutation/list of axes).

### Inputs and notation

* Gray code vertices (h_w\in V_k), or just the step axis (d_w) where (h_{w+1}=h_w\vplus \mathbf e_{d_w}).
* mismatch state (s_w\in V_k).
* axis-order list (D_w): a list/permutation of ([0,1,\dots,k-1]).
* basis vector (\mathbf e_i) is the bitvector with a 1 in coordinate (i).
* (\vplus) is XOR.

### Axis-order update rules (the Bradley part)

**Bubble update (move-to-front):**
[
D_{w}^{+} ;=; \text{Bubble}(D_w,d_w) ;:=; [d_w] ;\Vert; [x\in D_w:;x\neq d_w].
]

**Ring update (rotate-to-front):**
Let (j) be the index such that (D_w[j]=d_w). Then
[
D_{w}^{+} ;=; \text{Ring}(D_w,d_w) ;:=; D_w[j:];\Vert;D_w[:j].
]

((\Vert) means list concatenation.)

### Choosing (a_w) and updating (s_w)

Given (d_w) and current (s_w):

1. Update the axis order (D_w \mapsto D_w^{+}) using Bubble or Ring.
2. Choose the mismatch-step axis (a_w) by:
   [
   a_w :=
   \begin{cases}
   d_w, & \text{if }(s_w)*{d_w}=0\quad\text{(forced)}\
   D_w^{+}[1], & \text{if }(s_w)*{d_w}=1\quad\text{(free, pick “next” axis)}
   \end{cases}
   ]
   (For (k=1), the free case does not occur; for (k\ge2), (D_w^{+}[1]\neq d_w).)
3. Then:
   [
   s_{w+1} = s_w \vplus \mathbf e_{a_w}.
   ]

This **always** satisfies your Lemma’s constraints:

* If ((s_w)*{d_w}=0), flipping (d_w) makes ((s*{w+1})_{d_w}=1).
* If ((s_w)*{d_w}=1), flipping any other bit keeps ((s*{w+1})_{d_w}=1).

### Optional simplification for Ring (no need to store (D_w) if you fix a cyclic order)

If you fix the cyclic order once and for all as
[
D_0 = [k-1,k-2,\dots,0],
]
then Ring rotation makes the “next” axis after (d_w) equal to ((d_w-1)\bmod k). So Ring can be written purely as:
[
s_{w+1} =
\begin{cases}
s_w \vplus \mathbf e_{d_w}, & (s_w)*{d_w}=0,[4pt]
s_w \vplus \mathbf e*{(d_w-1)\bmod k}, & (s_w)_{d_w}=1,
\end{cases}
]
and you do not need to cache (D_w).

Bubble generally **cannot** be reduced to a formula involving only (d_w) (it depends on the history of which axes have been moved to the front), so caching (D_w) is the right way.

## Recommendation for integrating into `article.tex`

* Present Bubble/Ring as **policies for selecting (a_w)** in the mismatch walk when the choice is free.
* Make the construction explicitly parameterized by a function:
  [
  a_w = \texttt{PickAxis}(s_w,d_w,\text{cached state}),
  ]
  with Bubble/Ring as concrete implementations.
* If you want Bubble “faithfully,” place it under the **general affine automorphism** framework (A(x)=Px\vplus a), not only cyclic (T_{e,d}).

If you want, I can also express the above directly in your paper’s notation and style (as a lemma + algorithm environment), but the core recurrence you asked for is exactly the three-line rule:
[
D_w^+ = {\text{Bubble or Ring}}(D_w,d_w),\quad
a_w = \begin{cases} d_w,&(s_w)*{d_w}=0\ D_w^+[1],&(s_w)*{d_w}=1\end{cases},\quad
s_{w+1}=s_w\vplus \mathbf e_{a_w}.
]
