We now have data on discontinuities in the Hamilton Hilbert curve in hamilton_discontinuities.csv.
These were created using hamilton_metrics.c.
Let's analyze
 them. Make a Python file discontinuities.py and use it to read the CSV file and 
generate plots: a point plot of number of discontinuities as a function of domain 
area for 2d, number of discontinuities as a function of domain boundary for 2d, 
number of discontinuities as a function of domain volume for 3d, number of 
discontinuities as a function of surface area in 3d. point plot of log of maximum 
jump size as a function of the maximum side length for 2d, point plot of log of 
maximum jump size as a function of maximum side length for 3d, plot of geometric 
average of jump size as a function of geometric average of side lengths for 2d and
 3d. Make the Python file so that it has a main that will either make all plots 
with the argument `--all-plots` or will make individual plots, where each plot is 
made using a different argument, like `--number-by-area-2d`. It's ok if the names 
are long. Write plots to PDF files and PNG files (both). Read the input CSV using 
a hardcoded name.

"Continue implementing the plan in /home/node/.claude/plans/zazzy-popping-nebula.md for Haverkort metrics"

These were important files:
Plan: /home/node/.claude/plans/zazzy-popping-nebula.md
Metrics doc: /workspace/comments/20251230a_metrics.md
Existing pattern: /workspace/src/hamilton_metrics.c