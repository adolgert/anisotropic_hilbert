#!/bin/bash
#
# range_query_clustering.sh
#
# Complete run script for range-query clustering analysis.
# Compares Hamilton-CHI vs LC-CHI curves on clustering performance.
#
# Usage:
#   ./range_query_clustering.sh [OPTIONS]
#
# Options:
#   --num-sets N    Number of table sets per curve type (default: 1)
#   --output FILE   Output CSV file (default: range_query_clustering_results.csv)
#   --skip-tables   Skip table generation (use existing hilbert_tables.h5)
#   --help          Show this help

set -e

# Defaults
NUM_SETS=1
OUTPUT="range_query_clustering_results.csv"
SKIP_TABLES=0
HDF5_FILE="hilbert_tables.h5"

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --num-sets)
            NUM_SETS="$2"
            shift 2
            ;;
        --output)
            OUTPUT="$2"
            shift 2
            ;;
        --skip-tables)
            SKIP_TABLES=1
            shift
            ;;
        --help)
            sed -n '2,15p' "$0" | sed 's/^# //' | sed 's/^#//'
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

echo "========================================"
echo "Range-Query Clustering Analysis"
echo "========================================"
echo "Output file: $OUTPUT"
echo "HDF5 tables: $HDF5_FILE"
echo "Table sets per type: $NUM_SETS"
echo

# Step 1: Build required programs
echo "=== Step 1: Building programs ==="
make generate_fast_tables 2>/dev/null || make generate_fast_tables
make range_query_clustering 2>/dev/null || make range_query_clustering
echo "Build complete."
echo

# Step 2: Generate HDF5 tables (if not skipping)
if [ "$SKIP_TABLES" -eq 0 ]; then
    echo "=== Step 2: Generating Hilbert curve tables ==="
    ./generate_hilbert_curves.sh "$HDF5_FILE" "$NUM_SETS"
    echo
else
    echo "=== Step 2: Skipping table generation (using existing $HDF5_FILE) ==="
    if [ ! -f "$HDF5_FILE" ]; then
        echo "ERROR: $HDF5_FILE not found. Remove --skip-tables or generate tables first."
        exit 1
    fi
    echo "Tables found:"
    h5ls "$HDF5_FILE" 2>/dev/null || echo "  (h5ls not available)"
    echo
fi

# Step 3: Run clustering analysis
echo "=== Step 3: Running range-query clustering analysis ==="
./range_query_clustering --output "$OUTPUT"
echo

# Step 4: Summary
echo "=== Step 4: Results Summary ==="
echo "Output written to: $OUTPUT"
echo
echo "Row count by curve type:"
tail -n +2 "$OUTPUT" | cut -d',' -f1 | sort | uniq -c
echo
echo "Sample results (first 10 rows):"
head -11 "$OUTPUT" | column -t -s','
echo
echo "Done."
