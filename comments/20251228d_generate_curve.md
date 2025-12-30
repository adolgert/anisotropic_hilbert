# Review of Curve Generation

Below is a faithful mathematical description of what `build_tables()` is doing, expressed in the same “two-bit” language ((h,\ell)\in \mathrm{GF}(2)^n\times \mathrm{GF}(2)^n) with XOR (\oplus).

Throughout, let (n=k) be the dimension. The lattice is
[
V={0,1,2,3}^n.
]
Write every lattice vertex (x\in V) as
[
x = 2h + \ell,\qquad h,\ell\in{0,1}^n\cong \mathrm{GF}(2)^n
]
(componentwise), where (h) is the **parent cube** (high bit per axis) and (\ell) is the **local corner** (low bit per axis). This is exactly what the code computes as:

* `parent_pos_mask(coord)` (\equiv h)
* `local_mask(coord)` (\equiv \ell)

Let the parent Gray order be a sequence
[
g[0],g[1],\dots,g[2^n-1]\in \mathrm{GF}(2)^n,
]
and let (\mathrm{rank}(p)) be its inverse (the code’s `gray_rank`). Then the (w)-th visited child cube is the set
[
C_w := { (h,\ell)\ :\ h=g[w],\ \ell\in \mathrm{GF}(2)^n}.
]
The code stores (\mathrm{rank}(h)) for each lattice vertex as `parent_index[id]`.

Also define the unique parent step dimension
[
d_w \text{ such that } g[w+1]=g[w]\oplus e_{d_w},\qquad w=0,\dots,2^n-2,
]
where (e_i) is the (i)-th unit vector.

---

## (a) Why it is correct to build a graph “from exit to exit”

### The key local adjacency facts in ((h,\ell)) language

In the (4)-ary lattice, an edge changes exactly one coordinate by (\pm1). Translated into ((h,\ell)):

1. **Internal edge within a fixed child cube** (h) (does not change the parent cube):
   [
   (h,\ell)\ \longleftrightarrow\ (h,\ell\oplus e_a)
   \quad\text{for some axis }a.
   ]
   So “one internal hop” is “flip exactly one bit of (\ell)”.

2. **Boundary-crossing edge** from cube (h) to its neighbor (h\oplus e_d) across axis (d) exists exactly on the shared face (the (1\leftrightarrow 2) boundary), and it flips both high and low bits in that axis:
   [
   (h,\ell)\ \longleftrightarrow\ (h\oplus e_d,\ \ell\oplus e_d),
   ]
   but only when the vertex is on the shared face, i.e. when its (d)-coordinate is 1 or 2 (equivalently (\ell_d = 1-h_d)).

### What a two-level curve looks like abstractly

A valid two-level Hilbert-like curve with this setup decomposes as, for each cube (w):

* you **enter** cube (C_w) at some local corner (\ell^{\text{in}}_w),
* you traverse a Hamilton path on the hypercube (Q_n) (a Gray code) inside (C_w),
* you **exit** cube (C_w) at some local corner (\ell^{\text{out}}_w),
* you cross one boundary edge into cube (C_{w+1}) (for (w<2^n-1)).

Your assumption (“child Gray codes start at local origin and end along an axis”) is, in this formalism:
[
\ell^{\text{out}}_w = \ell^{\text{in}}*w \oplus e*{a_w}
\quad\text{for some } a_w\in{0,\dots,n-1}.
\tag{1}
]
So the only per-cube degrees of freedom that matter to global continuity are:

* the entry corner (\ell^{\text{in}}_w),
* the exit direction (a_w) (equivalently the exit corner).

All *other* edges inside the cube are “fillable” by choosing an appropriate oriented Gray code, as long as (1) holds.

### The contraction argument the code is using

The C++ code constructs a directed graph whose vertices are lattice vertices (x\in{0,1,2,3}^n), but it only allows forward edges that represent:

* leaving cube (w) at an **exit vertex** (X_w),
* crossing into cube (w+1) to an **entry vertex** (E_{w+1}),
* taking **one internal hop** to select the next cube’s **exit vertex** (X_{w+1}).

In ((h,\ell)) notation, a graph edge corresponds to a length-2 segment
[
(h_w,\ell^{\text{out}}*w)\ \to\ (h*{w+1},\ell^{\text{in}}*{w+1})\ \to\ (h*{w+1},\ell^{\text{out}}*{w+1})
]
with
[
(h*{w+1},\ell^{\text{in}}*{w+1}) = (h_w\oplus e*{d_w},\ \ell^{\text{out}}*w\oplus e*{d_w}),
\tag{2}
]
and
[
\ell^{\text{out}}*{w+1} = \ell^{\text{in}}*{w+1} \oplus e_{a_{w+1}}.
\tag{3}
]

So the graph search is really searching over *choices of exit corners*, and it bakes in the “one internal hop” condition so that (3) is automatically satisfied.

**Correctness (informal but exact):**

* (**Soundness**) Any full two-level curve induces a sequence of per-cube exit vertices ((X_0,\dots,X_{2^n-1})) that satisfies exactly these local constraints, hence induces a path in the exit-to-exit graph.

* (**Completeness**) Conversely, any path in this exit-to-exit graph fixes, for every cube, an entry corner and an adjacent exit corner. Under the assumption “a Gray-code Hamilton path exists for any adjacent endpoint pair up to orientation,” you can fill each cube with an oriented child Gray code, and the boundary edges between cubes connect by construction. Thus a path in the exit-graph lifts to a full curve.

That is why it is correct to search in the “exit-to-exit” compressed graph: it is exactly the quotient of the full problem by the fact that intra-cube Hamiltonicity is guaranteed once endpoints are adjacent.

---

## (b) How many ways does an exit connect to the next exit?

There are three different “counts” here, and the code is only committing to some of them.

### (b1) Is the boundary crossing from cube (w) to cube (w+1) unique?

Yes (given the exit vertex).

Cubes (C_w) and (C_{w+1}) differ in exactly one parent bit (d_w). They share exactly one ((n!-!1))-dimensional face. If an exit vertex lies on that face, then it has **exactly one** neighbor across the face (change coordinate (1\leftrightarrow 2) in that axis). In ((h,\ell)) form, (2) is unique:
[
(h_w,\ell^{\text{out}}*w)\mapsto(h_w\oplus e*{d_w},\ \ell^{\text{out}}*w\oplus e*{d_w}).
]
So the entry corner in the next cube is determined uniquely by the current exit.

### (b2) Given the entry in cube (w+1) and the chosen next exit vertex, is the “one internal hop” unique?

Yes (if it exists).

Inside a cube, neighbors differ by flipping exactly one local bit:
[
(h,\ell)\leftrightarrow(h,\ell\oplus e_a).
]
So if (E_{w+1}=(h_{w+1},\ell^{\text{in}}*{w+1})) and (X*{w+1}=(h_{w+1},\ell^{\text{out}}*{w+1})) are adjacent, then the axis
[
a*{w+1} = \text{the unique index with } \ell^{\text{out}}*{w+1}=\ell^{\text{in}}*{w+1}\oplus e_{a_{w+1}}
]
is unique. This is what the code computes via
`step = e_local ^ x_local` and `popcount(step)==1`, then `ctz(step)`.

So: for a fixed pair of consecutive exit vertices ((X_w,X_{w+1})) that the graph connects, the implied length-2 segment (X_w\to E_{w+1}\to X_{w+1}) is unique.

### (b3) Are there multiple *choices* for the next exit (X_{w+1})?

Generally yes.

Even though the boundary crossing (X_w\to E_{w+1}) is unique, from (E_{w+1}) there are up to (n) internal neighbors. Among those, several might be valid “exit vertices” of cube (w+1) (i.e., lie on the face toward cube (w+2)). Each such neighbor corresponds to a different choice of (a_{w+1}) and hence a different child orientation choice later.

This multiplicity is exactly the branching factor of the directed graph the code constructs.

### (b4) After fixing entry and exit corners for a cube, is the child orientation unique?

No.

Even if you fix endpoints (\ell^{\text{in}}_w) and (\ell^{\text{out}}_w=\ell^{\text{in}}*w\oplus e*{a_w}), there are usually many Hamilton paths (Gray codes) inside (Q_n) with those endpoints.

If you take one fixed canonical child Gray code with endpoints (0\to e_0) and allow all hypercube automorphisms (bit flips + coordinate permutations), the number of automorphisms mapping that directed edge to a particular directed edge is ((n-1)!) (choose a permutation sending axis (0) to axis (a_w), the remaining (n-1) axes can be permuted arbitrarily). So even at the “oriented canonical Gray code” level, it is not unique.

The code does not try to enumerate these; it only records:

* entry corner (`child_entry[w] = e_local`)
* exit axis (`child_dir[w] = d`)

---

## (c) High-level algorithm as a LaTeX `algorithm`/`algorithmic` snippet

This matches `build_tables()` + `derive()` at the right level (search over exit vertices, then derive entry masks and exit directions):

```latex
\begin{algorithm}
\caption{Derive child-entry corners and exit directions for a 2-level $4^n$ curve}
\begin{algorithmic}[1]
\REQUIRE Dimension $n$; parent Gray order $g[0..2^n\!-\!1]\subset \mathrm{GF}(2)^n$ with $g[0]=0$
\ENSURE Tables $\mathrm{entry}[w]\in \mathrm{GF}(2)^n$, $\mathrm{dir}[w]\in\{0,\dots,n-1\}$

\STATE Define $V := \{0,1,2,3\}^n$
\STATE For each $x\in V$, write $x = 2h(x)+\ell(x)$ with $h(x),\ell(x)\in\mathrm{GF}(2)^n$
\STATE Compute $\mathrm{rank}:\mathrm{GF}(2)^n\to\{0,\dots,2^n-1\}$ s.t.\ $\mathrm{rank}(g[w])=w$
\STATE Define layer index $w(x) := \mathrm{rank}(h(x))$
\STATE $s \gets (0,\dots,0)$ \COMMENT{start vertex in $V$}
\STATE $f \gets (3g[2^n\!-\!1]_0,\dots,3g[2^n\!-\!1]_{n-1})$ \COMMENT{finish corner in $V$}

\STATE Define $\mathrm{Exit}(x)$ to be true iff $x=f$ or $\exists y\sim x$ with $w(y)=w(x)+1$
\STATE Initialize directed graph $G$ on vertex set $V$

\FORALL{$x\in V$ with $\mathrm{Exit}(x)$ and $w(x)<2^n-1$}
  \FORALL{$y\sim x$ with $w(y)=w(x)+1$} \COMMENT{cross into next cube}
    \FORALL{$z\sim y$ with $w(z)=w(y)$ and $\mathrm{Exit}(z)$} \COMMENT{one internal hop to an exit}
      \STATE Add directed edge $x\to z$ to $G$
    \ENDFOR
  \ENDFOR
\ENDFOR

\STATE Add edges $s\to z$ for all $z\sim s$ with $w(z)=0$ and $\mathrm{Exit}(z)$
\STATE Find a directed path $P=(s,X_0,X_1,\dots,X_{2^n-1})$ in $G$ with $X_{2^n-1}=f$
\IF{no such $P$ exists} \STATE \textbf{fail} \ENDIF

\STATE Set $\mathrm{entry}[0]\gets \ell(s)$
\FOR{$w=0$ \TO $2^n-1$}
  \IF{$w>0$}
    \STATE $d \gets \text{index of the $1$ in } g[w-1]\oplus g[w]$
    \STATE $E_w \gets \text{the unique neighbor of }X_{w-1}\text{ in cube }w \text{ across axis }d$
    \STATE $\mathrm{entry}[w]\gets \ell(E_w)$
  \ENDIF
  \STATE $\ell_{\mathrm{out}}\gets \ell(X_w)$
  \STATE $t \gets \mathrm{entry}[w]\oplus \ell_{\mathrm{out}}$
  \STATE $\mathrm{dir}[w]\gets \text{index of the $1$ in }t$ \COMMENT{require $\mathrm{wt}(t)=1$}
\ENDFOR

\RETURN $(\mathrm{entry},\mathrm{dir})$
\end{algorithmic}
\end{algorithm}
```

This is intentionally close to the code’s logic:

* `Exit(x)` corresponds to `is_exit[id]`
* the “two-step” edges correspond to the nested loops “cross boundary” then “internal hop”
* the final loop corresponds to `derive()` computing `child_entry` and `child_dir`.

---

## (d) Improvements

### 1) Replace the (4^n)-vertex graph with a (2^n)-state graph (major asymptotic win)

The code’s graph has up to (4^n) vertices and builds edges by scanning geometric neighbors. For (n\le 7) it’s fine; for larger (n) it becomes the bottleneck.

You can compress the entire search into a walk on (\mathrm{GF}(2)^n) using the state
[
s_w := h_w \oplus \ell^{\text{in}}_w\in\mathrm{GF}(2)^n,
]
where (h_w=g[w]).

Then one can derive the transition rule (equivalent to what the geometry loops are enforcing):

* choosing exit direction (a_w) flips one bit of (s):
  [
  s_{w+1} = s_w \oplus e_{a_w};
  ]
* feasibility of crossing from cube (w) to (w+1) forces:
  [
  (s_{w+1})_{d_w} = 1.
  ]

So for each step (w), from state (s_w) you can go to any neighbor (s_{w+1}) of Hamming distance 1 whose (d_w)-bit is 1.

This gives a layered directed graph on only (2^n) states per layer (or even reuse states with time-dependent constraint), and you can DP/BFS it in (O(2^n\cdot n \cdot 2^n)) worst-case or better with a layered predecessor table. In practice, it’s drastically smaller than (4^n).

Once you have (s_w) and (a_w), you recover the tables with:
[
\ell^{\text{in}}_w = h_w \oplus s_w,\qquad \mathrm{dir}[w]=a_w.
]

### 2) Avoid geometric neighbor scanning; compute exits algebraically

In the current code, `is_exit[id]` is computed by checking whether a lattice vertex has *any* neighbor in the next cube.

But for cube (w\to w+1), the shared-face condition is just one bit test in ((h,\ell)) language:
[
\ell^{\text{out}}*{w,d_w} = 1 - h*{w,d_w}.
]
So you can enumerate exit corners for cube (w) directly (there are exactly (2^{n-1}) of them per cube, except the last which is fixed by finish), without touching the full (4^n) lattice.

### 3) Exploit the fact the graph is layered (no need for generic BFS on a big adjacency list)

All edges go from cube index (w) to (w+1). That means:

* the graph is a DAG,
* any successful path has fixed length (2^n).

So you can do a simple forward DP:

* for each layer (w), maintain the set of reachable exits,
* store predecessor pointers,
* stop once the last layer is reached.

This avoids building a full Boost graph and can be done with compact arrays.

### 4) If you want “nonstandard” solutions, make that a first-class objective

The current heuristic (“try unrestricted BFS; if it yields standard, force the first exit to a different neighbor”) is weak: it biases only the first cube.

Better approaches:

* **Randomized DP/BFS tie-breaking** on the compressed (s)-state graph (or exit-corner graph), to sample many different solutions.
* **Enumerate** all solutions or count them by DP (still feasible for moderate (n)), then select one uniformly or by a scoring function.
* Score objectives: maximize/minimize certain symmetries, avoid standard tables, maximize axis variety in `child_dir`, etc.

### 5) Store edge labels and remove the recomputation pass (`derive()`)

Right now the edge construction implicitly chooses:

* which boundary axis was crossed,
* which internal axis was used for the one-hop exit selection.

But that information is not stored on the edge; it’s reconstructed later.

You can store on each directed edge:

* the entry local mask (\ell^{\text{in}}_{w+1}),
* the internal axis (a_{w+1}),

and then you don’t need to recompute via `coord_from_id` + `local_mask` + popcount checks.

This also makes correctness checks cleaner: the derived data is exactly the data you used to build the edge.

---

If you want, I can rewrite the algorithm in purely (\mathrm{GF}(2)^n) terms (no ({0,1,2,3}^n) lattice at all), equivalent to what the C++ code is searching for, and show the explicit mapping between a found exit-path and the per-cube ((\ell^{\text{in}}_w,a_w)) sequence the tables encode.

