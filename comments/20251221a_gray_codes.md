# Gray Code Symmetry

## Preliminaries

Represent the matrix of the Binary-reflected gray code (BRGC)
with $M$. Use Greek letters if it's in $V_n=GF(2)^n$ and Roman for integers. Convert an integer to $GF(2)^n$ using the function $b(i)=\iota$.

## Reflection Symemtry

- First binary vector: $\beta=\mathbf{0}$, $\gamma=0$.
- Last binary vector: $\beta=\mathbf{1}$, $\gamma=\epsilon_{n-1}$.

Here $\epsilon_{n-1}$ represents the unit vector in the last position,
also called the most-significant bit.

The reflection symmetry rule is that the complement of the input bits will flip the most-sigificant bit (MSB).
$$
g(\beta + \mathbf{1}) = M(\beta + \mathbf{1})=M\beta + M\mathbf{1}
=g(\beta)+\epsilon_{n-1}.
$$

## Parity

Parity is the number of bits in a gray code. It's $\mathbf{1}^T\cdot \nu$. The parity of a Gray code is equal to the last
bit of the input $\beta$.

## Shadow Symmetry

$V_n=GF(2)^n$ is a hypercube $Q_n$. The Gray code symmetry allows you to decompose this space.

Because of the reflection property, the Gray code for $n$ bits is composed of two copies of the sequence for $n-1$ bits.

- **First Half:** The standard sequence on a subspace where MSB=0.
- **Second Half:** The reverse sequence on a subspace where MSB=1.

In $GF(2)$ notation, if we split the vector into the MSB $\gamma_{n-1}$ and the remaining vector,

- For the first $2^{n-1}$ steps: $\gamma=[0, \gamma_{n-1}(t)]$. Here the odd vector notation is the first bit and then the rest of the bits.
- For the second $2^{n-1}$ steps: $\gamma=[1,\gamma_{n-1}(2^n-1-t)]$.

Note there is a "totally balanced gray code" that fixes the flaw where the LSB flips much more often than the MSB.

## Erasing the Least Significant Bit

The position of the entry point in Hamilton's formulation rests on
an equation that erases the least significant bit, so what is this
Gray code?

If you erase the LSB, the resulting sequence is the $(n-1)$-bit Gray code where every value is repeated twice.

### Matrix Proof

If you remove the bottom row of the matrix form of the Gray code and the last column, the remaining structure is still a Gray code.
The truncated vector is
$$
  \gamma_{\text{trunc}} = M_{n-1}\rho^{-1}\beta
$$
Here $\rho$ is a rotation of the indices. The text says
$\gamma_{\text{trunc}} = M_{n-1}\cdot(b>>1)$, and I'm translating that.

### The Ruler Function

In the BRGC, the position of the bit that changes at step $i$ follows
the "Ruler function" (or the exponent of the highest power of 2
dividing $i$). The sequence of bit flip positions is
(1-based, where 1 is LSB)
$$
1, 2, 1, 3, 1, 2, 1, 4, 1,\ldots
$$
Notice that the LSB flips at every odd step. The other bits (positions >1) flip at every even step.

### Geometric Interpretation

Imagine the 3D cube $Q_3$ sitting on a table. The Gray code is a path that visits every corner. "Erasing the LSB" is geometrically equivalent to shining a light from the top and looking at the shadow of the path on the floor (projecting $Q_n​\rightarrow Q_{n−1}$).

- When the path moves "vertically" (along the z-axis/LSB), the shadow stays in the same spot.

- When the path moves "horizontally" (along x or y), the shadow moves to a new corner.

Because the BRGC alternates strictly between "vertical" moves and "horizontal" moves, the shadow creates the "Step-Wait-Step-Wait" pattern you observed.

## Backwards Walk

To walk the Gray code backward, you walk the Gray code forward and flip the most significant bit.
$$
 g_{\text{rev}}(t) = g(t)\oplus \epsilon_{\text{MSB}}
$$
Geometrically: This corresponds to reflecting the hypercube across the hyperplane perpendicular to the MSB axis. It is a "mirror image" symmetry, not a rotational one.

## The Hidden Rotational Symmetry (The Transitions)

There is one part of the code that is symmetric in the way you might be hoping: the sequence of changes.

If you write down which bit changes at each step (the transition sequence), that sequence is a palindrome.

- Forward Steps (n=3): 0, 1, 0, 2, 0, 1, 0

- Backward Steps (n=3): 0, 1, 0, 2, 0, 1, 0

(Using 0-based indexing for bits)

So, while the coordinate values (GF(2)n vectors) do not match under rotation, the rhythm of the walk is identical forward and backward.