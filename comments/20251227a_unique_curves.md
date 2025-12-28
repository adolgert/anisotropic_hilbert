[Download `generate_hilbert_tables.cpp`](sandbox:/mnt/data/generate_hilbert_tables.cpp)
[Download generated lookup header `hilbert_generated_tables.h`](sandbox:/mnt/data/hilbert_generated_tables.h)

## What this produces

For each dimension (k \in {2,3,4,5,6,7}), the generator emits four tables of length (2^k):

* `HILBERT_GRAY_k[w]`
  The Gray-code vertex label (bitmask in ([0,2^k))) for child index `w` (the subcube order).

* `HILBERT_RANK_k[g]`
  The inverse map: the `w` such that `HILBERT_GRAY_k[w] == g`.

* `HILBERT_CHILD_ENTRY_k[w]`
  The entry corner (cube-local vertex) for child `w`, as a (k)-bit mask.

* `HILBERT_CHILD_DIR_k[w]`
  The “internal direction” for child `w` (the axis bit that flips between the child’s entry and its exit), as an integer in `[0, k-1]`.

These tables come from a Boost-Graph-based layered-DAG search (the same structure your `construct.jl` is exploiting): nodes are the (4^k) “(parent-bit, child-bit)” corners; edges jump from an exit corner in cube `w` to a compatible exit corner in cube `w+1` via the required boundary hop and the required “one hop inside the next cube”.

The emitted tables are **not** Hamilton’s closed-form `child_entry/child_dir`; the generator deliberately tries to pick an **alternative** solution when one exists.

## How to plug this into your C code

You have two separable pieces in `hilbert_affine.c`:

1. the Gray order `w <-> g` (`gray_code_axis0`, `gray_decode_axis0`)
2. the child geometry / orientation update (`child_entry`, `child_dir`)

If you want to be able to swap *both* without assuming BRGC, replace both with table lookups.

### Minimal integration patch sketch

1. Include the generated header:

```c
#include "hilbert_generated_tables.h"
```

2. Replace Gray encode/decode at a level:

**Decode path** (currently):

```c
uint32_t g = gray_code_axis0(w, parent_k);
```

Replace with:

```c
uint32_t g = hilbert_gray(parent_k, w);
```

**Encode path** (currently):

```c
uint32_t w = gray_decode_axis0(pre, parent_k);
```

Replace with:

```c
uint32_t w = hilbert_rank(parent_k, pre);
```

3. Replace child geometry access:

Where you currently do:

```c
uint32_t entry = child_entry(w) & parent_mask;
uint32_t dchild = child_dir(w, parent_k);
```

Replace with:

```c
uint32_t entry  = hilbert_child_entry(parent_k, w) & parent_mask;
uint32_t dchild = hilbert_child_dir(parent_k, w);
```

That is exactly the separation you were describing: “Gray code” is now purely `HILBERT_GRAY_k / HILBERT_RANK_k`, while “child geometry” is purely `HILBERT_CHILD_ENTRY_k / HILBERT_CHILD_DIR_k`.

## What to modify to explore more curves

In `generate_hilbert_tables.cpp`, the only place that “assumes BRGC” is the line that builds the Gray order:

```cpp
gray[w] = gray_code_axis0(w, k);
```

If you replace the `gray` vector with *any* Hamiltonian path on (Q_k) (starting at 0, ending at whatever corner you want to be the global endpoint), the rest of the construction stays the same:

* `rank` is computed from `gray`
* the exit-vertex DAG is built from “cube index = rank[parent_pos]”
* BFS finds a compatible sequence of exits
* `child_entry/child_dir` are derived from that exit sequence

That is the “constraint on the Gray curve” in executable form:

* For a proposed Gray order (G), build the exit-DAG.
* If there is **no** start→finish path, then **no** child-geometry table of the “adjacent endpoints / one-hop-internal-edge” type exists for that (G) (within this model).

If you want *multiple* alternatives for the same (G), the exit-DAG is acyclic and layered, so you can enumerate or sample paths by:

* computing reachability counts per node (DP from the end), then
* walking forward choosing among outgoing edges that still reach the end.

The current generator just forces an alternative by trying different “first exit from the origin” candidates and keeping the first non-standard solution it finds.

## Files produced here

* `generate_hilbert_tables.cpp`: Boost Graph generator (builds the layered exit-DAG and BFS’s a path).
* `hilbert_generated_tables.h`: ready-to-include lookup tables + dispatch helpers:

  * `hilbert_gray(k,w)`
  * `hilbert_rank(k,g)`
  * `hilbert_child_entry(k,w)`
  * `hilbert_child_dir(k,w)`

If you want the generator to enforce **dimension-embedding consistency** (your “(k+\Delta) contains (k)” idea), that becomes an additional constraint on the path search (you constrain the allowed exits/entries on the face where the extra axes are fixed). The same DAG framework supports that; it just needs extra filtering before adding edges.
