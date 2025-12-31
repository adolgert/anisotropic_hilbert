# Block Bounding-Box Statistics

This tool computes practical R-tree block bounding-box statistics for space-filling curves, measuring how well consecutive curve points cluster spatially when packed into fixed-size blocks.

## Background

R-trees and similar spatial indexes organize points into blocks (leaf nodes) of B consecutive points along a space-filling curve. Each block has an axis-aligned bounding box. Query performance depends on minimizing total bounding-box area—smaller bounding boxes mean fewer false-positive disk accesses during range queries.

Reference: Haverkort & van Walderveen (2010), Section 3.4 "Total bounding box measures"

## Building

```bash
cd src
make bounding_box_stats
```

## Running

```bash
# Output to stdout
./bounding_box_stats

# Output to CSV file
./bounding_box_stats --output results.csv

# Show help
./bounding_box_stats --help
```

## Metrics

For each curve, domain, and block size B, the tool computes:

| Metric | Definition | Ideal Value |
|--------|------------|-------------|
| `mean_area_ratio` | mean(bbox_area / B) over all blocks | 1.0 |
| `p95_area_ratio` | 95th percentile of (bbox_area / B) | ~1.0 |
| `max_area_ratio` | max(bbox_area / B) | ~1.0 |
| `max_peri_ratio` | max(bbox_perimeter / sqrt(B)) | ~4.0 |

An `area_ratio` of 1.0 means the bounding box contains exactly B points (perfect packing). Values > 1.0 indicate wasted space in the bounding box.

## Test Configuration

**Domains** (all 262,144 points):
- D0: 512×512 (aspect 1:1, equal dimensions)
- D1: 2048×128 (aspect 16:1)
- D2: 4096×64 (aspect 64:1)
- D3: 8192×32 (aspect 256:1)

**Block sizes**:
- Power-of-2: 32, 64, 128, 256, 512, 1024 (align with recursive structure)
- Non-power-of-2: 33, 100, 500 (straddle recursive boundaries)

**Curves**:
- Hamilton-CHI: Original compact Hilbert index (has seam discontinuities)
- LC-CHI-BRGC: Lattice-continuous corrected version

## Key Results

For **square domains** (D0), both curves perform identically.

For **rectangular domains** (D1-D3) with non-power-of-2 block sizes, Hamilton-CHI shows catastrophic worst-case behavior:

| Domain | Aspect | Hamilton max_area_ratio | LC-CHI max_area_ratio |
|--------|--------|------------------------|----------------------|
| D0 | 1:1 | 1.94 | 1.94 |
| D1 | 16:1 | **527.5** | 1.94 |
| D2 | 64:1 | **131.9** | 1.94 |
| D3 | 256:1 | **38.8** | 1.94 |

Hamilton's seam jumps cause blocks straddling discontinuities to have bounding boxes **20-270× larger** than expected. This directly impacts R-tree query performance.

## Output Format

CSV with columns:
```
curve,dims,m0,m1,m2,total_points,block_size,mean_area_ratio,p95_area_ratio,max_area_ratio,max_peri_ratio
```

Example row:
```
Hamilton-CHI,2,11,7,0,262144,33,2.373699,1.939394,527.515152,91.913002
```

## Algorithm

1. Decode all N points along the curve (O(N))
2. Partition into ceil(N/B) consecutive blocks
3. For each block:
   - Compute axis-aligned bounding box (min/max per dimension)
   - Compute bbox_area = product of side lengths
   - Compute bbox_perimeter = 2 × sum of side lengths
4. Aggregate statistics across all blocks

Total complexity: O(N) per curve/domain/block-size combination.

## Interpretation

- **Power-of-2 block sizes** show `area_ratio = 1.0` for both curves because blocks align perfectly with the Hilbert curve's recursive structure.

- **Non-power-of-2 block sizes** reveal the true clustering quality because blocks straddle recursive boundaries.

- **Hamilton's elevated mean** (2.3-2.5 vs 1.4) on rectangular domains indicates that seam discontinuities affect enough blocks to raise the average, not just isolated worst cases.

- **LC-CHI's consistent behavior** (max ~1.94 regardless of aspect ratio) demonstrates the practical benefit of lattice continuity for spatial indexing applications.
