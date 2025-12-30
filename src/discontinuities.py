#!/usr/bin/env python3
"""
discontinuities.py

Analyze Hamilton Hilbert curve discontinuities and generate plots.

Reads hamilton_discontinuities.csv and produces various visualizations
comparing discontinuity counts and jump sizes against domain properties.
"""

import argparse
import sys
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt


CSV_FILE = "hamilton_discontinuities.csv"


def load_data():
    """Load the discontinuities CSV file and compute derived columns."""
    df = pd.read_csv(CSV_FILE)

    # Compute side lengths from bit counts (2^m)
    df['side0'] = 2 ** df['m0']
    df['side1'] = 2 ** df['m1']
    df['side2'] = 2 ** df['m2'].fillna(0).astype(int)

    # 2D metrics
    df['area_2d'] = df['side0'] * df['side1']
    df['perimeter_2d'] = 2 * (df['side0'] + df['side1'])
    df['max_side_2d'] = df[['side0', 'side1']].max(axis=1)
    df['geom_mean_side_2d'] = np.sqrt(df['side0'] * df['side1'])

    # 3D metrics (only valid for 3D data)
    df['volume_3d'] = df['side0'] * df['side1'] * df['side2']
    df['surface_area_3d'] = 2 * (df['side0'] * df['side1'] +
                                  df['side1'] * df['side2'] +
                                  df['side0'] * df['side2'])
    df['max_side_3d'] = df[['side0', 'side1', 'side2']].max(axis=1)
    df['geom_mean_side_3d'] = (df['side0'] * df['side1'] * df['side2']) ** (1/3)

    return df


def save_plot(fig, basename):
    """Save figure to both PDF and PNG formats."""
    fig.savefig(f"{basename}.pdf", bbox_inches='tight')
    fig.savefig(f"{basename}.png", bbox_inches='tight', dpi=150)
    print(f"Saved {basename}.pdf and {basename}.png")


def plot_discontinuities_by_area_2d(df):
    """Plot number of discontinuities vs domain area for 2D cases."""
    df_2d = df[df['dims'] == 2].copy()

    fig, ax = plt.subplots(figsize=(8, 6))
    ax.scatter(df_2d['area_2d'], df_2d['discontinuity_count'],
               alpha=0.6, edgecolors='black', linewidths=0.5)
    ax.set_xlabel('Domain Area (cells)')
    ax.set_ylabel('Number of Discontinuities')
    ax.set_title('Hamilton CHI Discontinuities vs Domain Area (2D)')
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.grid(True, alpha=0.3)

    # Handle zero values in log scale
    nonzero = df_2d['discontinuity_count'] > 0
    if nonzero.any():
        ax.scatter(df_2d.loc[nonzero, 'area_2d'],
                   df_2d.loc[nonzero, 'discontinuity_count'],
                   alpha=0.6, edgecolors='black', linewidths=0.5, c='C0')
    zero_disc = df_2d[~nonzero]
    if len(zero_disc) > 0:
        ax.scatter(zero_disc['area_2d'],
                   [0.5] * len(zero_disc),  # Plot at 0.5 for visibility
                   alpha=0.6, edgecolors='black', linewidths=0.5, c='green',
                   marker='v', label='Zero discontinuities')
        ax.legend()

    save_plot(fig, 'discontinuities_by_area_2d')
    plt.close(fig)


def plot_discontinuities_by_perimeter_2d(df):
    """Plot number of discontinuities vs domain perimeter for 2D cases."""
    df_2d = df[df['dims'] == 2].copy()

    fig, ax = plt.subplots(figsize=(8, 6))

    nonzero = df_2d['discontinuity_count'] > 0
    if nonzero.any():
        ax.scatter(df_2d.loc[nonzero, 'perimeter_2d'],
                   df_2d.loc[nonzero, 'discontinuity_count'],
                   alpha=0.6, edgecolors='black', linewidths=0.5, c='C0')
    zero_disc = df_2d[~nonzero]
    if len(zero_disc) > 0:
        ax.scatter(zero_disc['perimeter_2d'],
                   [0.5] * len(zero_disc),
                   alpha=0.6, edgecolors='black', linewidths=0.5, c='green',
                   marker='v', label='Zero discontinuities')
        ax.legend()

    ax.set_xlabel('Domain Perimeter (cells)')
    ax.set_ylabel('Number of Discontinuities')
    ax.set_title('Hamilton CHI Discontinuities vs Domain Perimeter (2D)')
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.grid(True, alpha=0.3)

    save_plot(fig, 'discontinuities_by_perimeter_2d')
    plt.close(fig)


def plot_discontinuities_by_volume_3d(df):
    """Plot number of discontinuities vs domain volume for 3D cases."""
    df_3d = df[df['dims'] == 3].copy()

    fig, ax = plt.subplots(figsize=(8, 6))

    nonzero = df_3d['discontinuity_count'] > 0
    if nonzero.any():
        ax.scatter(df_3d.loc[nonzero, 'volume_3d'],
                   df_3d.loc[nonzero, 'discontinuity_count'],
                   alpha=0.6, edgecolors='black', linewidths=0.5, c='C0')
    zero_disc = df_3d[~nonzero]
    if len(zero_disc) > 0:
        ax.scatter(zero_disc['volume_3d'],
                   [0.5] * len(zero_disc),
                   alpha=0.6, edgecolors='black', linewidths=0.5, c='green',
                   marker='v', label='Zero discontinuities')
        ax.legend()

    ax.set_xlabel('Domain Volume (cells)')
    ax.set_ylabel('Number of Discontinuities')
    ax.set_title('Hamilton CHI Discontinuities vs Domain Volume (3D)')
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.grid(True, alpha=0.3)

    save_plot(fig, 'discontinuities_by_volume_3d')
    plt.close(fig)


def plot_discontinuities_by_surface_area_3d(df):
    """Plot number of discontinuities vs surface area for 3D cases."""
    df_3d = df[df['dims'] == 3].copy()

    fig, ax = plt.subplots(figsize=(8, 6))

    nonzero = df_3d['discontinuity_count'] > 0
    if nonzero.any():
        ax.scatter(df_3d.loc[nonzero, 'surface_area_3d'],
                   df_3d.loc[nonzero, 'discontinuity_count'],
                   alpha=0.6, edgecolors='black', linewidths=0.5, c='C0')
    zero_disc = df_3d[~nonzero]
    if len(zero_disc) > 0:
        ax.scatter(zero_disc['surface_area_3d'],
                   [0.5] * len(zero_disc),
                   alpha=0.6, edgecolors='black', linewidths=0.5, c='green',
                   marker='v', label='Zero discontinuities')
        ax.legend()

    ax.set_xlabel('Domain Surface Area (cells)')
    ax.set_ylabel('Number of Discontinuities')
    ax.set_title('Hamilton CHI Discontinuities vs Surface Area (3D)')
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.grid(True, alpha=0.3)

    save_plot(fig, 'discontinuities_by_surface_area_3d')
    plt.close(fig)


def plot_max_jump_by_max_side_2d(df):
    """Plot log of max jump size vs max side length for 2D cases."""
    df_2d = df[(df['dims'] == 2) & (df['max_distance'] > 0)].copy()

    fig, ax = plt.subplots(figsize=(8, 6))
    ax.scatter(df_2d['max_side_2d'], df_2d['max_distance'],
               alpha=0.6, edgecolors='black', linewidths=0.5)

    ax.set_xlabel('Maximum Side Length (cells)')
    ax.set_ylabel('Maximum Jump Distance (L1)')
    ax.set_title('Hamilton CHI Max Jump vs Max Side Length (2D)')
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.grid(True, alpha=0.3)

    save_plot(fig, 'max_jump_by_max_side_2d')
    plt.close(fig)


def plot_max_jump_by_max_side_3d(df):
    """Plot log of max jump size vs max side length for 3D cases."""
    df_3d = df[(df['dims'] == 3) & (df['max_distance'] > 0)].copy()

    fig, ax = plt.subplots(figsize=(8, 6))
    ax.scatter(df_3d['max_side_3d'], df_3d['max_distance'],
               alpha=0.6, edgecolors='black', linewidths=0.5)

    ax.set_xlabel('Maximum Side Length (cells)')
    ax.set_ylabel('Maximum Jump Distance (L1)')
    ax.set_title('Hamilton CHI Max Jump vs Max Side Length (3D)')
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.grid(True, alpha=0.3)

    save_plot(fig, 'max_jump_by_max_side_3d')
    plt.close(fig)


def plot_geom_mean_jump_by_geom_mean_side_2d(df):
    """Plot geometric mean of jump size vs geometric mean of side lengths (2D)."""
    df_2d = df[(df['dims'] == 2) & (df['geom_mean_distance'] > 0)].copy()

    fig, ax = plt.subplots(figsize=(8, 6))
    ax.scatter(df_2d['geom_mean_side_2d'], df_2d['geom_mean_distance'],
               alpha=0.6, edgecolors='black', linewidths=0.5)

    ax.set_xlabel('Geometric Mean of Side Lengths (cells)')
    ax.set_ylabel('Geometric Mean of Jump Distances (L1)')
    ax.set_title('Hamilton CHI Geom Mean Jump vs Geom Mean Side (2D)')
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.grid(True, alpha=0.3)

    save_plot(fig, 'geom_mean_jump_by_geom_mean_side_2d')
    plt.close(fig)


def plot_geom_mean_jump_by_geom_mean_side_3d(df):
    """Plot geometric mean of jump size vs geometric mean of side lengths (3D)."""
    df_3d = df[(df['dims'] == 3) & (df['geom_mean_distance'] > 0)].copy()

    fig, ax = plt.subplots(figsize=(8, 6))
    ax.scatter(df_3d['geom_mean_side_3d'], df_3d['geom_mean_distance'],
               alpha=0.6, edgecolors='black', linewidths=0.5)

    ax.set_xlabel('Geometric Mean of Side Lengths (cells)')
    ax.set_ylabel('Geometric Mean of Jump Distances (L1)')
    ax.set_title('Hamilton CHI Geom Mean Jump vs Geom Mean Side (3D)')
    ax.set_xscale('log')
    ax.set_yscale('log')
    ax.grid(True, alpha=0.3)

    save_plot(fig, 'geom_mean_jump_by_geom_mean_side_3d')
    plt.close(fig)


# Registry of all plot functions
PLOT_FUNCTIONS = {
    'discontinuities-by-area-2d': plot_discontinuities_by_area_2d,
    'discontinuities-by-perimeter-2d': plot_discontinuities_by_perimeter_2d,
    'discontinuities-by-volume-3d': plot_discontinuities_by_volume_3d,
    'discontinuities-by-surface-area-3d': plot_discontinuities_by_surface_area_3d,
    'max-jump-by-max-side-2d': plot_max_jump_by_max_side_2d,
    'max-jump-by-max-side-3d': plot_max_jump_by_max_side_3d,
    'geom-mean-jump-by-geom-mean-side-2d': plot_geom_mean_jump_by_geom_mean_side_2d,
    'geom-mean-jump-by-geom-mean-side-3d': plot_geom_mean_jump_by_geom_mean_side_3d,
}


def main():
    parser = argparse.ArgumentParser(
        description='Analyze Hamilton Hilbert curve discontinuities and generate plots.',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python discontinuities.py --all-plots
  python discontinuities.py --discontinuities-by-area-2d
  python discontinuities.py --max-jump-by-max-side-3d --geom-mean-jump-by-geom-mean-side-2d
"""
    )

    parser.add_argument('--all-plots', action='store_true',
                        help='Generate all plots')

    for plot_name in PLOT_FUNCTIONS:
        parser.add_argument(f'--{plot_name}', action='store_true',
                            help=f'Generate {plot_name.replace("-", " ")} plot')

    args = parser.parse_args()

    # Check if any plot was requested
    plot_requested = args.all_plots or any(
        getattr(args, plot_name.replace('-', '_')) for plot_name in PLOT_FUNCTIONS
    )

    if not plot_requested:
        parser.print_help()
        sys.exit(1)

    # Load data
    print(f"Loading data from {CSV_FILE}...")
    df = load_data()
    print(f"Loaded {len(df)} rows ({len(df[df['dims']==2])} 2D, {len(df[df['dims']==3])} 3D)")

    # Generate requested plots
    if args.all_plots:
        print("Generating all plots...")
        for plot_name, plot_func in PLOT_FUNCTIONS.items():
            plot_func(df)
    else:
        for plot_name, plot_func in PLOT_FUNCTIONS.items():
            arg_name = plot_name.replace('-', '_')
            if getattr(args, arg_name):
                plot_func(df)

    print("Done!")


if __name__ == '__main__':
    main()
