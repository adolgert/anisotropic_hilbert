#!/bin/bash
#
# generate_hilbert_curves.sh
#
# Generate multiple Hilbert curve table sets for each Gray code type.
# Each set uses a different random seed to produce different valid geometries.
#
# Output: hilbert_tables.h5 containing:
#   /brgc/0..99/1..8/{gray,gray_rank,child_entry,child_dir}
#   /monotone/0..99/1..8/{gray,gray_rank,child_entry,child_dir}
#   /balanced/0..99/1..8/{gray,gray_rank,child_entry,child_dir}
#   /random/0..99/1..8/{gray,gray_rank,child_entry,child_dir}

set -e

OUTPUT="${1:-hilbert_tables.h5}"
NUM_SETS="${2:-100}"

echo "Generating $NUM_SETS sets for each Gray code type..."
echo "Output file: $OUTPUT"
echo

# Remove existing file to start fresh
rm -f "$OUTPUT"

# Generate tables for each type
for gray_type in brgc monotone balanced random; do
    echo "=== Generating $gray_type tables ==="
    for i in $(seq 0 $((NUM_SETS - 1))); do
        # Use different seed for each set
        seed=$((12345 + i * 1000))

        if [ $((i % 10)) -eq 0 ]; then
            echo "  $gray_type: $i/$NUM_SETS (seed=$seed)"
        fi

        # First set creates the file, subsequent sets append
        if [ "$gray_type" = "brgc" ] && [ "$i" -eq 0 ]; then
            ./generate_fast_tables --output "$OUTPUT" --gray "$gray_type" --name "$gray_type" --index "$i" --seed "$seed"
        else
            ./generate_fast_tables --output "$OUTPUT" --gray "$gray_type" --name "$gray_type" --index "$i" --seed "$seed" --append
        fi
    done
    echo "  $gray_type: done"
    echo
done

echo "=== Summary ==="
echo "Generated $NUM_SETS sets for each of: brgc, monotone, balanced, random"
echo "Total: $((NUM_SETS * 4)) table sets"
echo "Output: $OUTPUT"

# Show file structure
if command -v h5ls &> /dev/null; then
    echo
    echo "=== File structure ==="
    h5ls -r "$OUTPUT" 2>/dev/null | head -30
    echo "..."
fi
