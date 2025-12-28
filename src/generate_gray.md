# Gray Code Generator

A C++ library for generating different types of Gray codes on hypercubes.

## What It Is

A **Gray code** is a Hamiltonian path on the n-dimensional hypercube $Q_k$, where consecutive vertices differ by exactly one bit. This library generates Gray codes of dimension $k$ (for $k = 1$ to $7$) with different properties:

| Type | Description | Guarantee |
|------|-------------|-----------|
| **BRGC** | Binary Reflected Gray Code | Always works, O(1) per element |
| **Monotone** | Hamming weight non-decreasing every 2 steps | Falls back to BRGC if search fails |
| **Balanced** | Each axis flipped approximately equally | Falls back to BRGC if search fails |
| **Random** | Random cyclic Gray code from seed | Always works (via automorphism fallback) |

All generated codes are:
- **Cyclic**: First and last vertices are adjacent
- **Start at 0**: The path begins at vertex 0
- **Complete**: All $2^k$ vertices visited exactly once

For $k = 1$, the Gray code is simply `[0, 1]` - the unique Hamiltonian cycle on a single edge. This trivial case is included for completeness, as it's needed when the anisotropic Hilbert curve reduces to a single active axis. Note that for $k = 1$, all types (BRGC, Monotone, Balanced, Random) return the same result since there's only one possible Gray code.

## How to Build

```bash
cd src

# Build just the library object
make generate_gray.o

# Build and run tests
make test_gray

# Run with verbose output
make test_gray_verbose
```

## API

### Header

```cpp
#include "generate_gray.h"
```

### Types

```cpp
namespace graygen {
    using u32 = uint32_t;
    using u64 = uint64_t;

    enum class GrayCodeType { BRGC, Monotone, Balanced, Random };
}
```

### Generation Functions

```cpp
// Generate specific types (k = dimension, 1-7)
std::vector<u32> generate_brgc(int k);
std::vector<u32> generate_monotone(int k);
std::vector<u32> generate_balanced(int k);
std::vector<u32> generate_random(int k, u64 seed);

// Convenience wrapper
std::vector<u32> gray_code(int k, GrayCodeType type, u64 seed = 0);
```

The returned vector has length $2^k$, where `gray[w]` is the vertex (as a $k$-bit mask) at position `w` in the path.

### Verification Functions

```cpp
bool verify_gray_code(const std::vector<u32>& gray, int k);  // Valid Hamiltonian path
bool verify_cyclic(const std::vector<u32>& gray, int k);     // First/last adjacent
bool verify_monotone(const std::vector<u32>& gray);          // Weight constraint
bool verify_balanced(const std::vector<u32>& gray, int k, int tolerance = 2);
```

### Utility Functions

```cpp
std::vector<u32> compute_inverse(const std::vector<u32>& gray);  // gray_rank[v] = position of v
std::vector<int> compute_transition_counts(const std::vector<u32>& gray, int k);

inline u32 popcount32(u32 x);      // Hamming weight
inline int hamming_dist(u32 a, u32 b);  // Number of differing bits
```

## Examples

### Basic Usage

```cpp
#include "generate_gray.h"
#include <iostream>

int main() {
    using namespace graygen;

    // Generate BRGC for 3 dimensions (8 vertices)
    auto gray = generate_brgc(3);

    // Print the path: 0 -> 1 -> 3 -> 2 -> 6 -> 7 -> 5 -> 4
    for (u32 v : gray) {
        std::cout << v << " ";
    }
    std::cout << std::endl;

    return 0;
}
```

### Random Gray Code with Seed

```cpp
#include "generate_gray.h"

int main() {
    using namespace graygen;

    // Same seed gives same result
    auto gray1 = generate_random(5, 12345);
    auto gray2 = generate_random(5, 12345);
    assert(gray1 == gray2);

    // Different seed gives different result
    auto gray3 = generate_random(5, 67890);
    assert(gray1 != gray3);

    return 0;
}
```

### Integration with Hilbert Tables

```cpp
#include "generate_gray.h"

// In generate_hilbert_tables.cpp, replace:
//   auto gray = gray_axis0_seq(k);
// With:
//   auto gray = graygen::generate_random(k, seed);
// Or:
//   auto gray = graygen::gray_code(k, graygen::GrayCodeType::Balanced);
```

## Algorithm Details

### BRGC
Standard formula: `gray[w] = w ^ (w >> 1)`

### Monotone
Uses iterative backtracking with Warnsdorff heuristic, constrained so that `popcount(gray[i]) <= popcount(gray[i+2])`. This ensures the path oscillates between adjacent Hamming weight levels without going backwards.

**Limitation**: The search space is highly constrained; for $k \geq 3$, the algorithm often fails to find a solution within the iteration limit and falls back to BRGC.

### Balanced
Uses iterative backtracking that tracks transition counts per axis and prefers under-used axes. Target is $2^k / k$ transitions per axis with tolerance $\pm 2$.

**Limitation**: Works reliably for $k \leq 4$; for larger $k$, the balance constraint is difficult to satisfy and falls back to BRGC.

### Random
1. Attempts iterative Hamiltonian path search with shuffled neighbor ordering
2. Uses Warnsdorff heuristic (prefer vertices with fewer unvisited neighbors)
3. On failure, applies a random hypercube automorphism to BRGC:
   - Random axis permutation
   - Random bit-flip mask (XOR)
   - Rotation to start at vertex 0

This guarantees a valid cyclic Gray code for any seed.

## References

- Savage, C. D. "A Survey of Combinatorial Gray Codes." SIAM Review 39.4 (1997): 605-629.
- Savage, C. D., and P. Winkler. "Monotone Gray codes and the middle levels problem." J. Combinatorial Theory A 70.2 (1995): 230-248.
- Mutze, T. "Combinatorial Gray codes - an updated survey." arXiv:2202.01280 (2022).
