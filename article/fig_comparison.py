"""
fig_comparison.py

Publication-quality figure comparing Hamilton's buggy compact Hilbert curve
with the corrected lattice-continuous version.

Usage:
    python fig_comparison.py              # Display figure
    python fig_comparison.py --save       # Save as PDF
    python fig_comparison.py --save=png   # Save as PNG

Potential tweaks (let me know if you want any):
  1. Adjust figure size/aspect ratio
  2. Change color scheme (colorblind-friendly palette)
  3. Add coordinate annotations at the discontinuity
  4. Remove/modify the index labels
  5. Different arrow styles
  6. Export to TikZ via pgf backend for LaTeX integration
"""

import argparse
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.collections import LineCollection, PatchCollection
import numpy as np

# Import both implementations
import compact_hilbert as buggy
import anisotropic_hilbert as correct


def get_path_segments(points):
    """Convert list of points to line segments for LineCollection."""
    segments = []
    for i in range(len(points) - 1):
        segments.append([points[i], points[i + 1]])
    return segments


def classify_segments(points):
    """Classify segments as continuous (L1=1) or discontinuous (L1>1)."""
    continuous = []
    discontinuous = []
    for i in range(len(points) - 1):
        p1, p2 = points[i], points[i + 1]
        dist = abs(p1[0] - p2[0]) + abs(p1[1] - p2[1])
        if dist == 1:
            continuous.append([p1, p2])
        else:
            discontinuous.append([p1, p2])
    return continuous, discontinuous


def draw_grid(ax, width, height, color='#e0e0e0', linewidth=0.5):
    """Draw background grid lines."""
    for x in range(width + 1):
        ax.axvline(x, color=color, linewidth=linewidth, zorder=0)
    for y in range(height + 1):
        ax.axhline(y, color=color, linewidth=linewidth, zorder=0)


def draw_lattice_points(ax, width, height, color='#404040', size=30):
    """Draw lattice points as dots."""
    for x in range(width):
        for y in range(height):
            ax.scatter(x, y, c=color, s=size, zorder=3, edgecolors='white', linewidths=0.5)


def draw_path_with_arrows(ax, points, color='#2563eb', linewidth=2,
                          discontinuous_color='#dc2626', show_discontinuities=True):
    """Draw the path with arrows indicating direction."""
    continuous, discontinuous = classify_segments(points)

    # Draw continuous segments
    if continuous:
        lc = LineCollection(continuous, colors=color, linewidths=linewidth, zorder=2)
        ax.add_collection(lc)

    # Draw discontinuous segments (dashed, red)
    if discontinuous and show_discontinuities:
        lc_disc = LineCollection(discontinuous, colors=discontinuous_color,
                                  linewidths=linewidth, linestyles='dashed', zorder=2)
        ax.add_collection(lc_disc)

    # Add direction arrows at midpoints of some segments
    arrow_indices = list(range(0, len(points) - 1, max(1, len(points) // 8)))
    for i in arrow_indices:
        p1, p2 = np.array(points[i]), np.array(points[i + 1])
        mid = (p1 + p2) / 2
        direction = p2 - p1
        dist = np.abs(direction).sum()

        # Normalize and scale arrow
        if dist > 0:
            direction = direction / dist * 0.15
            c = discontinuous_color if dist > 1 and show_discontinuities else color
            ax.annotate('', xy=mid + direction, xytext=mid - direction,
                       arrowprops=dict(arrowstyle='->', color=c, lw=1.5),
                       zorder=4)


def draw_start_end_markers(ax, points, start_color='#16a34a', end_color='#dc2626'):
    """Mark start and end points."""
    # Start point (green square)
    ax.scatter([points[0][0]], [points[0][1]], c=start_color, s=100,
               marker='s', zorder=5, edgecolors='white', linewidths=1.5)

    # End point (red diamond)
    ax.scatter([points[-1][0]], [points[-1][1]], c=end_color, s=100,
               marker='D', zorder=5, edgecolors='white', linewidths=1.5)


def add_index_labels(ax, points, fontsize=7, offset=(0.15, 0.15)):
    """Add small index labels near each point."""
    for h, (x, y) in enumerate(points):
        ax.text(x + offset[0], y + offset[1], str(h), fontsize=fontsize,
                color='#666666', ha='left', va='bottom', zorder=6)


def create_comparison_figure(m=(3, 1), figsize=(12, 5)):
    """
    Create side-by-side comparison of buggy and corrected algorithms.

    Parameters
    ----------
    m : tuple
        Box exponents (e.g., (3, 1) for 8x2 box)
    figsize : tuple
        Figure size in inches
    """
    width, height = 1 << m[0], 1 << m[1]

    # Get paths from both algorithms
    buggy_points = list(buggy.iter_points(m))
    correct_points = list(correct.iter_points(m))

    # Count discontinuities
    buggy_disc = buggy.check_continuity(m)

    # Create figure with two subplots
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=figsize)

    # Style settings
    path_color = '#2563eb'  # Blue
    disc_color = '#dc2626'  # Red

    # === Left panel: Buggy (Hamilton's original) ===
    ax1.set_title(f"Hamilton's Algorithm (2008)\n{len(buggy_disc)} discontinuit{'y' if len(buggy_disc) == 1 else 'ies'}",
                  fontsize=12, fontweight='bold', color='#333333')

    draw_grid(ax1, width, height)
    draw_lattice_points(ax1, width, height)
    draw_path_with_arrows(ax1, buggy_points, color=path_color,
                          discontinuous_color=disc_color, show_discontinuities=True)
    draw_start_end_markers(ax1, buggy_points)
    add_index_labels(ax1, buggy_points)

    # === Right panel: Corrected ===
    ax2.set_title("Corrected Algorithm\n(lattice-continuous)",
                  fontsize=12, fontweight='bold', color='#333333')

    draw_grid(ax2, width, height)
    draw_lattice_points(ax2, width, height)
    draw_path_with_arrows(ax2, correct_points, color=path_color,
                          show_discontinuities=True)
    draw_start_end_markers(ax2, correct_points)
    add_index_labels(ax2, correct_points)

    # Configure axes
    for ax in (ax1, ax2):
        ax.set_xlim(-0.5, width - 0.5)
        ax.set_ylim(-0.5, height - 0.5)
        ax.set_aspect('equal')
        ax.set_xlabel('x', fontsize=10)
        ax.set_ylabel('y', fontsize=10)

        # Clean up ticks
        ax.set_xticks(range(width))
        ax.set_yticks(range(height))
        ax.tick_params(axis='both', which='both', length=0)

        # Remove spines
        for spine in ax.spines.values():
            spine.set_visible(False)

    # Add legend
    legend_elements = [
        mpatches.Patch(facecolor=path_color, label='Continuous step (L¹=1)'),
        mpatches.Patch(facecolor=disc_color, label='Discontinuity (L¹>1)'),
        plt.Line2D([0], [0], marker='s', color='w', markerfacecolor='#16a34a',
                   markersize=10, label='Start (h=0)'),
        plt.Line2D([0], [0], marker='D', color='w', markerfacecolor='#dc2626',
                   markersize=10, label=f'End (h={len(buggy_points)-1})'),
    ]
    fig.legend(handles=legend_elements, loc='lower center', ncol=4,
               frameon=False, fontsize=9, bbox_to_anchor=(0.5, -0.02))

    # Add box shape annotation
    fig.suptitle(f'Compact Hilbert Index on {width}×{height} Grid (m = {m})',
                 fontsize=14, fontweight='bold', y=1.02)

    plt.tight_layout()
    return fig


def main():
    parser = argparse.ArgumentParser(description='Generate Hilbert curve comparison figure')
    parser.add_argument('--save', nargs='?', const='pdf', default=None,
                        help='Save figure (default: pdf, or specify format)')
    parser.add_argument('--m', type=str, default='3,1',
                        help='Box exponents as comma-separated values (default: 3,1 for 8x2)')
    parser.add_argument('--dpi', type=int, default=300,
                        help='DPI for raster output (default: 300)')
    args = parser.parse_args()

    # Parse m
    m = tuple(int(x) for x in args.m.split(','))

    # Create figure
    fig = create_comparison_figure(m=m)

    if args.save:
        filename = f'hilbert_comparison_{m[0]}x{m[1]}.{args.save}'
        fig.savefig(filename, dpi=args.dpi, bbox_inches='tight',
                    facecolor='white', edgecolor='none')
        print(f'Saved: {filename}')
    else:
        plt.show()


if __name__ == '__main__':
    main()
