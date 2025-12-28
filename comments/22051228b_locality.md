Here is the reformatted response with all mathematical notation and equations using LaTeX delimiters.

To measure these properties for a new Hilbert curve, you need to rely on two distinct categories of metrics: Clustering/Locality metrics (how well the curve keeps spatial neighbors together in the index) and Box-to-Curve Ratios (how compact the 1D intervals are when folded back into 2D space).

Here are the specific references and methodologies for measuring both.

Part A: Measuring Spatial Locality

In the literature, "spatial locality" is usually measured by how many separate "chunks" (continuous index intervals) are required to retrieve a compact 2D shape (like a query rectangle).

1. The Clustering Number (Moon et al.)

This is the "gold standard" metric for database and indexing applications. It measures how fragmented a spatial query becomes when mapped to the curve.

Reference: Moon, B., Jagadish, H. V., Faloutsos, C., & Saltz, J. H. (2001). Analysis of the clustering properties of the Hilbert space-filling curve. IEEE Transactions on Knowledge and Data Engineering.

How they measure it:

They define the Clustering Number $C$ as the number of continuous runs of Hilbert indices required to cover a query region $Q$.

The Test: Generate a set of random query rectangles (or arbitrary polyhedra) in the space.

The Metric: For each query, identify all points inside the rectangle. Group these points into continuous sequences of Hilbert indices. Count the number of sequences.

Formula: For a grid of side $N$ and a query rectangle of size $X \times Y$, the expected number of clusters for a standard Hilbert curve is approximately:

$$C \approx \frac{\text{Perimeter}(Q)}{2}$$

Goal: A lower clustering number is better. You can measure your new curve against this baseline.

2. The Gotsman-Lindenbaum Metric (Distance Preservation)

This measures locality in terms of mathematical distance ratios (Lipschitz conditions), useful if you are analyzing the curve's analytical properties rather than database performance.

Reference: Gotsman, C., & Lindenbaum, M. (1996). On the metric properties of discrete space-filling curves. IEEE Transactions on Image Processing.

How they measure it:

They measure the ratio between the distance in 1D index space and the distance in 2D Euclidean space.

$$L = \max_{i, j} \frac{d_{curve}(i, j)}{d_{Euclidean}(P_i, P_j)^2}$$

(Note: The square power depends on the dimension; for 2D it is squared).

Part B: The Bounding Box Problem

You defined this as "using a sequence of points defined by neighboring Hilbert indices and measuring the bounding box." In academic literature, this is formally known as the Box-to-Curve Ratio (BCR) or the Worst-Case Bounding Box Area (WBA).

This is the critical metric for R-tree performance (specifically the Hilbert R-Tree). If a sequence of indices produces a bounding box that is mostly "empty space," the curve is inefficient.

1. Box-to-Curve Ratio (Haverkort)

Herman Haverkort is the leading authority on this specific metric. His work explicitly analyzes the bounding boxes of contiguous Hilbert segments.

Reference: Haverkort, H. (2010). Locality and Bounding-Box Quality of Two-Dimensional Space-Filling Curves. (Also see Bos & Haverkort, Hyperorthogonal Well-Folded Hilbert Curves, 2015).

How they measure it:

They define a segment $S$ as a contiguous set of indices on the curve (e.g., from index $100$ to $200$).

The Metric: The Box-to-Curve Ratio (BCR) for a segment $S$ is:

$$\text{BCR}(S) = \frac{\text{Area}(\text{BoundingBox}(S))}{\text{Area}(S)}$$

(Where $\text{Area}(S)$ is the area of the domain covered by the curve segment—conceptually, if the curve is traversing a grid, this is the number of cells visited $\times$ the area of one cell).

The Evaluation: You must calculate the Worst-Case BCR (the maximum BCR over all possible segments $S$) and the Average BCR.

Benchmark:

The standard 2D Hilbert curve has a worst-case BCR of roughly $6$ (depending on exact definitions of the limit).

"Harmonious" Hilbert curves (a variant) achieve a worst-case BCR of $4$.

2. Packing Efficiency (Kamel & Faloutsos)

Reference: Kamel, I., & Faloutsos, C. (1994). Hilbert R-tree: An improved R-tree using fractals. VLDB.

How they measure it:

They measure the Perimeter or Area of the bounding boxes formed by the leaf nodes of an R-tree built using the curve.

The Test: Sort all data points by your new Hilbert index. Partition them into groups of size $B$ (page size).

The Metric: Sum the areas (or perimeters) of the bounding boxes of these groups.

Why: A "bad" curve will snake diagonally across the space, resulting in long, thin bounding boxes with huge dead space. A "good" curve (like standard Hilbert) creates square-like, compact boxes.

Summary of Next Steps

To validate your new curve, I recommend calculating the Box-to-Curve Ratio (BCR) as defined by Haverkort.

The Algorithm to measure BCR:

Discretize your space (e.g., $256 \times 256$ grid).

Traverse your new curve to get the sequence of coordinates: $P_0, P_1, \dots, P_N$.

Iterate through various window sizes $w$ (representing the "neighboring indices" length).

For every starting index $i$, consider the sub-sequence $S = \{P_i, \dots, P_{i+w}\}$.

Compute the Bounding Box of $S$ ($min_x, max_x, min_y, max_y$).

Calculate the metric:

$$\text{Metric} = \frac{\text{Area}(\text{Bounding Box})}{w}$$

Plot this metric. If your new curve has lower peaks than the standard Hilbert curve, you have improved the bounding box problem.