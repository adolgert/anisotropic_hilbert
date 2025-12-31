#!/usr/bin/env python3
"""
format_bbox_table.py

Reads bounding_box_stats_results.csv and outputs a LaTeX tabular snippet
for Table 4 (Practical block bounding-box statistics).

Usage:
    python format_bbox_table.py [input.csv] > table4.tex

If no input file specified, looks for ../src/bounding_box_stats_results.csv
"""

import csv
import sys
from pathlib import Path


def format_number(val, decimals=2):
    """Format a number with specified decimal places, removing trailing zeros."""
    if val == int(val):
        return str(int(val))
    formatted = f"{val:.{decimals}f}"
    # Remove trailing zeros after decimal point
    if '.' in formatted:
        formatted = formatted.rstrip('0').rstrip('.')
    return formatted


def domain_label(m0, m1):
    """Create a domain label like '8192×32' from m values."""
    width = 2 ** m0
    height = 2 ** m1
    return f"{width}$\\times${height}"


def main():
    # Determine input file
    if len(sys.argv) > 1:
        input_file = Path(sys.argv[1])
    else:
        input_file = Path(__file__).parent.parent / "src" / "bounding_box_stats_results.csv"

    if not input_file.exists():
        print(f"Error: Input file not found: {input_file}", file=sys.stderr)
        sys.exit(1)

    # Read CSV data
    rows = []
    with open(input_file, 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            rows.append(row)

    # Group by domain (m0, m1) and block_size
    # We want to show: Curve, Block size, mean, p95, max area ratio, max peri ratio

    # Get unique domains and block sizes
    domains = []
    seen_domains = set()
    for row in rows:
        key = (int(row['m0']), int(row['m1']))
        if key not in seen_domains:
            seen_domains.add(key)
            domains.append(key)

    # Select representative block sizes (32, 100, 500, 1024)
    selected_block_sizes = [32, 100, 500, 1024]

    # Build table data structure
    # Format: {(m0, m1, block_size): {curve: row_data}}
    table_data = {}
    for row in rows:
        m0, m1 = int(row['m0']), int(row['m1'])
        block_size = int(row['block_size'])
        curve = row['curve']

        if block_size not in selected_block_sizes:
            continue

        key = (m0, m1, block_size)
        if key not in table_data:
            table_data[key] = {}
        table_data[key][curve] = row

    # Output LaTeX table
    print("\\begin{tabular}{llrrrrr}")
    print("\\toprule")
    print("Domain & Curve & Block size $B$ & Mean $\\frac{\\text{bbox}}{B}$ & "
          "P95 $\\frac{\\text{bbox}}{B}$ & Max $\\frac{\\text{bbox}}{B}$ & "
          "Max $\\frac{\\text{peri}}{\\sqrt{B}}$ \\\\")
    print("\\midrule")

    curves = ['Hamilton-CHI', 'LC-CHI-BRGC']

    for m0, m1 in domains:
        domain = domain_label(m0, m1)
        first_row_for_domain = True

        for block_size in selected_block_sizes:
            key = (m0, m1, block_size)
            if key not in table_data:
                continue

            for curve in curves:
                if curve not in table_data[key]:
                    continue

                row = table_data[key][curve]

                mean_area = float(row['mean_area_ratio'])
                p95_area = float(row['p95_area_ratio'])
                max_area = float(row['max_area_ratio'])
                max_peri = float(row['max_peri_ratio'])

                # Format domain column (only show on first row for each domain)
                if first_row_for_domain:
                    domain_col = domain
                    first_row_for_domain = False
                else:
                    domain_col = ""

                # Shorten curve name for display
                curve_display = curve.replace('Hamilton-CHI', 'Hamilton').replace('LC-CHI-BRGC', 'LC-BRGC')

                print(f"{domain_col} & {curve_display} & {block_size} & "
                      f"{format_number(mean_area)} & {format_number(p95_area)} & "
                      f"{format_number(max_area)} & {format_number(max_peri)} \\\\")

        # Add a small separator between domains
        if (m0, m1) != domains[-1]:
            print("\\addlinespace")

    print("\\bottomrule")
    print("\\end{tabular}")


if __name__ == "__main__":
    main()
