#!/usr/bin/env python3
"""
range_query_format.py

Reads range_query_clustering_results.csv and outputs a LaTeX tabular snippet
for Table 5 (Range-query clustering on rectangular domains) for domain D2 (4096×64).

Usage:
    python range_query_format.py [input.csv] > table5.tex

If no input file specified, looks for range_query_clustering_results.csv in the same directory.
"""

import csv
import sys
from pathlib import Path


def format_number(val, decimals=2):
    """Format a number with specified decimal places, removing trailing zeros."""
    if abs(val - round(val)) < 0.001:
        return str(int(round(val)))
    formatted = f"{val:.{decimals}f}"
    # Remove trailing zeros after decimal point
    if '.' in formatted:
        formatted = formatted.rstrip('0').rstrip('.')
    return formatted


def query_window_label(w, h):
    """Create a query window label like '4×4' or '64×4'."""
    return f"{w}$\\times${h}"


def main():
    # Determine input file
    if len(sys.argv) > 1:
        input_file = Path(sys.argv[1])
    else:
        input_file = Path(__file__).parent / "range_query_clustering_results.csv"

    if not input_file.exists():
        print(f"Error: Input file not found: {input_file}", file=sys.stderr)
        sys.exit(1)

    # Read CSV data
    rows = []
    with open(input_file, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append(row)

    # Filter for domain D2: m0=12, m1=6 (4096×64)
    d2_rows = [r for r in rows if int(r['m0']) == 12 and int(r['m1']) == 6]

    if not d2_rows:
        print("Error: No data found for domain D2 (m0=12, m1=6)", file=sys.stderr)
        sys.exit(1)

    # Get unique query window sizes, preserving order from CSV
    query_sizes = []
    seen_sizes = set()
    for row in d2_rows:
        key = (int(row['query_w']), int(row['query_h']))
        if key not in seen_sizes:
            seen_sizes.add(key)
            query_sizes.append(key)

    # Build table data: {(query_w, query_h): {curve: row}}
    table_data = {}
    for row in d2_rows:
        qw, qh = int(row['query_w']), int(row['query_h'])
        curve = row['curve']
        key = (qw, qh)
        if key not in table_data:
            table_data[key] = {}
        table_data[key][curve] = row

    # Output LaTeX table matching the example format from the metrics doc
    # Columns: Curve | Query window (cells) | Mean clusters | p95 clusters | Max clusters | Sampling
    print("\\begin{tabular}{lrrrrl}")
    print("\\toprule")
    print("Curve & Query window & Mean clusters & P95 clusters & Max clusters & Method \\\\")
    print("\\midrule")

    curves = ['Hamilton-CHI', 'LC-CHI-BRGC', 'LC-CHI-Balanced', 'LC-CHI-Random']

    for qw, qh in query_sizes:
        if (qw, qh) not in table_data:
            continue

        query_label = query_window_label(qw, qh)

        for curve in curves:
            if curve not in table_data[(qw, qh)]:
                continue

            row = table_data[(qw, qh)][curve]

            mean_clusters = float(row['mean_clusters'])
            p95_clusters = float(row['p95_clusters'])
            max_clusters = int(row['max_clusters'])
            method = row['method']
            num_queries = int(row['num_queries'])

            # Shorten curve name for display
            curve_display = (curve
                .replace('Hamilton-CHI', 'Hamilton')
                .replace('LC-CHI-BRGC', 'LC-BRGC')
                .replace('LC-CHI-Balanced', 'LC-Balanced')
                .replace('LC-CHI-Random', 'LC-Random'))

            # Format method column
            if method == 'exhaustive':
                method_display = f"exhaustive ({num_queries:,})"
            else:
                method_display = method

            print(f"{curve_display} & {query_label} & "
                  f"{format_number(mean_clusters)} & {format_number(p95_clusters)} & "
                  f"{max_clusters} & {method_display} \\\\")

        # Add spacing between query size groups (except after last)
        if (qw, qh) != query_sizes[-1]:
            print("\\addlinespace")

    print("\\bottomrule")
    print("\\end{tabular}")


if __name__ == "__main__":
    main()
