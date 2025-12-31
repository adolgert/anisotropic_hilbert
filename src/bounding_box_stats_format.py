#!/usr/bin/env python3
"""
bounding_box_stats_format.py

Reads bounding_box_stats_results.csv and outputs a LaTeX tabular snippet
for Table 4 (Practical block bounding-box statistics) for domain D3 (8192×32).

Usage:
    python bounding_box_stats_format.py [input.csv] > table4.tex

If no input file specified, looks for bounding_box_stats_results.csv in the same directory.
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


def main():
    # Determine input file
    if len(sys.argv) > 1:
        input_file = Path(sys.argv[1])
    else:
        input_file = Path(__file__).parent / "bounding_box_stats_results.csv"

    if not input_file.exists():
        print(f"Error: Input file not found: {input_file}", file=sys.stderr)
        sys.exit(1)

    # Read CSV data
    rows = []
    with open(input_file, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append(row)

    # Filter for domain D3: m0=13, m1=5 (8192×32)
    d3_rows = [r for r in rows if int(r['m0']) == 13 and int(r['m1']) == 5]

    if not d3_rows:
        print("Error: No data found for domain D3 (m0=13, m1=5)", file=sys.stderr)
        sys.exit(1)

    # Group by block_size
    block_sizes = sorted(set(int(r['block_size']) for r in d3_rows))

    # Build table data: {block_size: {curve: row}}
    table_data = {}
    for row in d3_rows:
        bs = int(row['block_size'])
        curve = row['curve']
        if bs not in table_data:
            table_data[bs] = {}
        table_data[bs][curve] = row

    # Output LaTeX table matching the example format from the metrics doc
    # Columns: Curve | Block size (B) | mean bbox area / B | p95 bbox area / B | max bbox area / B | max bbox perimeter / sqrt(B)
    print("\\begin{tabular}{lrrrrr}")
    print("\\toprule")
    print("Curve & Block size $B$ & Mean $\\frac{\\text{bbox}}{B}$ & "
          "P95 $\\frac{\\text{bbox}}{B}$ & Max $\\frac{\\text{bbox}}{B}$ & "
          "Max $\\frac{\\text{peri}}{\\sqrt{B}}$ \\\\")
    print("\\midrule")

    curves = ['Hamilton-CHI', 'LC-CHI-BRGC']

    for block_size in block_sizes:
        if block_size not in table_data:
            continue

        for curve in curves:
            if curve not in table_data[block_size]:
                continue

            row = table_data[block_size][curve]

            mean_area = float(row['mean_area_ratio'])
            p95_area = float(row['p95_area_ratio'])
            max_area = float(row['max_area_ratio'])
            max_peri = float(row['max_peri_ratio'])

            # Shorten curve name for display
            curve_display = curve.replace('Hamilton-CHI', 'Hamilton').replace('LC-CHI-BRGC', 'LC-BRGC')

            print(f"{curve_display} & {block_size} & "
                  f"{format_number(mean_area)} & {format_number(p95_area)} & "
                  f"{format_number(max_area)} & {format_number(max_peri)} \\\\")

        # Add spacing between block size groups (except after last)
        if block_size != block_sizes[-1]:
            print("\\addlinespace")

    print("\\bottomrule")
    print("\\end{tabular}")


if __name__ == "__main__":
    main()
