This is a great idea. The tables are compact - for dimensions 2-7 you have:
Dimension	Table size	Total per dim
2D	4 entries	16 bytes
3D	8 entries	32 bytes
4D	16 entries	64 bytes
5D	32 entries	128 bytes
6D	64 entries	256 bytes
7D	128 entries	512 bytes
Total: ~1KB for all dimensions 2-7 with 4 tables each (gray, gray_rank, child_entry, child_dir). The table-based approach is elegant because:
Same algorithm, different tables: The encode/decode logic stays identical - you just swap which tables get looked up
Trivial to add new curves: Generate new tables, plug them in
No function pointer overhead: Direct array indexing is as fast as it gets
Self-documenting: The tables ARE the curve definition
Here's how I'd structure it:

```cpp
typedef struct {
    const uint8_t *gray;        // w -> gray code
    const uint8_t *gray_rank;   // gray code -> w (inverse)
    const uint8_t *child_entry; // w -> entry point
    const uint8_t *child_dir;   // w -> direction
} hilbert_tables_t;

typedef struct {
    hilbert_tables_t tables[MAX_DIMS + 1];  // indexed by k (dimension)
    int max_dim;  // highest dimension with tables
} hilbert_curve_variant_t;

// Then in hilbert_curve_t:
typedef struct {
    int mmax;
    int total_bits;
    int k_level[MAX_LEVELS + 1];
    int axes_ordered[MAX_DIMS];
    const hilbert_curve_variant_t *variant;  // <-- pointer to tables
} hilbert_curve_t;
```
The current computed functions (gray_code_axis0, child_entry, child_dir) would become just one variant - the "Hamilton" variant. Your alternative curve would be another variant with different tables. One question: Do you want to support dimensions > 7? The current computed approach handles arbitrary dimensions, while tables would need to either:
Pre-generate tables up to some max (e.g., 10D = 1024 entries = 4KB per table)
Fall back to computed for high dimensions
Limit to table-supported dimensions only
What's your typical use case for dimensions?
