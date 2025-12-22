## Derivation of the Contiguous Child Index Formula

### Setup

Consider a Hilbert curve on $P(m)$ with dimensions $(m_0, m_1, \ldots, m_{n-1})$. The Hilbert index $h$ is encoded as a sequence of variable-width digits:

$$h = (w_{m_{max}} \mid w_{m_{max}-1} \mid \cdots \mid w_1)$$

where $w_s$ is a $k_s$-bit digit and $k_s = |\{j : m_j \geq s\}|$ is the number of active axes at level $s$.

### Refinement: Increasing All Dimensions by 1

When we refine to $P(m+1)$ with dimensions $(m_0+1, m_1+1, \ldots, m_{n-1}+1)$:

**Claim:** The number of active axes at level $s$ in the refined curve is:
$$k'_s = |\{j : m_j + 1 \geq s\}| = |\{j : m_j \geq s-1\}|$$

Therefore:
- $k'_1 = |\{j : m_j \geq 0\}| = n$ (all axes active at the new finest level)
- $k'_{s+1} = k_s$ for $s \geq 1$ (levels shift up by one)

### Index Structure After Refinement

A point $p \in P(m)$ with Hilbert index $h$ corresponds to a cell that splits into $2^n$ children in $P(m+1)$.

In the refined curve, each child has index:
$$h' = (w'_{m_{max}+1} \mid w'_{m_{max}} \mid \cdots \mid w'_2 \mid w'_1)$$

**Key observation:** The encoding algorithm processes levels from coarsest to finest. When we add a new finest level:

1. The original digits determine the same coarse-to-fine path: $w'_{s+1} = w_s$ for all $s \in \{1, \ldots, m_{max}\}$

2. The new digit $w'_1$ at level 1 selects among the $2^n$ children within the cell

### The Formula

Writing out the index as a number:
$$h' = \underbrace{(w_{m_{max}} \mid \cdots \mid w_1)}_{\text{original } h} \mid w'_1$$

where $w'_1$ is an $n$-bit digit. This bit-concatenation is equivalent to:

$$\boxed{h' = h \cdot 2^n + w'_1, \qquad w'_1 \in \{0, 1, \ldots, 2^n - 1\}}$$

### Why Children Are Contiguous

The contiguity follows from the **hierarchical structure of the encoding**:

1. **Digits form a mixed-radix representation:** The Hilbert index is essentially a number where each "digit" position has a different base ($2^{k_s}$). The most significant digits (coarser levels) determine which large region you're in; the least significant digit (finest level) determines position within the smallest cell.

2. **Refinement adds a new least-significant digit:** When you refine, you're adding a new digit position at the bottom. All $2^n$ values of this new digit correspond to the children of the original cell, and they naturally form a contiguous block.

3. **No reordering across parent boundaries:** The transform $(e, d)$ and Gray code operations at level 1 permute which child gets which value of $w'_1$, but they don't mix children from different parents. The parent's index $h$ is already "baked in" to the higher digits.

### Summary

**Contiguous Child Index Formula:** For a cell with Hilbert index $i_0$ in $P(m)$, its $2^n$ children in $P(m+1)$ have Hilbert indices:

$$\{i_0 \cdot 2^n + j : j = 0, 1, \ldots, 2^n - 1\}$$

This holds regardless of the anisotropy $(m_0, \ldots, m_{n-1})$ because refinement always activates all $n$ axes at the new finest level.
