#!/usr/bin/env python3
r"""
Convert non-standard math markdown delimiters to standard LaTeX/Pandoc format.

Converts:
  - Standalone [ on a line  ->  \[
  - Standalone ] on a line  ->  \]
  - Inline (math...) where math contains LaTeX commands  ->  $math...$
    (but NOT inside display math blocks)
"""

import re
import sys
from pathlib import Path


def is_latex_math(content: str) -> bool:
    """Check if parenthesized content looks like LaTeX math."""
    # Empty content is not math
    if not content.strip():
        return False

    # Contains backslash commands like \ge, \oplus, \mathbb, etc.
    if re.search(r'\\[a-zA-Z]+', content):
        return True

    # Contains subscripts or superscripts
    if re.search(r'[_^]', content):
        return True

    # Short content (1-3 chars) that's just letters/numbers is likely a variable
    # e.g., (T), (k), (n), (e), (gc), (H_m)
    stripped = content.strip()
    if len(stripped) <= 3 and re.match(r'^[a-zA-Z0-9]+$', stripped):
        return True

    # Contains common math notation patterns
    # e.g., function calls like e(i), gc(w), comparisons, etc.
    if re.match(r'^[a-zA-Z]+\([^)]*\)$', stripped):  # function notation
        return True

    # Contains equals, inequalities, or other math operators
    if re.search(r'[=<>≤≥∈∉⊂⊃∪∩]', content):
        return True

    # Contains arithmetic with variables (like d+1, i-1, n*k)
    # Be careful: hyphenated words like "tie-break" should NOT match
    # Only match single-letter variables with operators, or digits with operators
    if re.search(r'(?<![a-zA-Z])[a-zA-Z][+*/][0-9]|[0-9][+\-*/][a-zA-Z](?![a-zA-Z])', stripped):
        return True
    # Single letter minus single letter or digit (but not hyphenated words)
    if re.search(r'(?<![a-zA-Z])[a-zA-Z]-[0-9a-zA-Z](?![a-zA-Z])', stripped):
        return True
    if re.search(r'\{[+\-]\}', stripped):  # {+} or {-}
        return True

    # Looks like it starts with "Theorem", "Lemma", "Algorithm", etc. - NOT math
    if re.match(r'^(Theorem|Lemma|Algorithm|Equation|Section|Chapter|not|and|or|this|hence|i\.e\.|e\.g\.)', stripped, re.IGNORECASE):
        return False

    # Contains quotes - probably not math
    if '"' in content or "'" in content:
        return False

    # Multiple English words (has spaces and common patterns) - not math
    if ' ' in stripped and re.search(r'\b(the|of|is|are|to|for|in|with|by|from|as|on|at)\b', stripped, re.IGNORECASE):
        return False

    return False


def convert_inline_math(line: str) -> str:
    """Convert inline (math) to $math$ where content looks like LaTeX."""
    result = []
    i = 0
    while i < len(line):
        if line[i] == '(':
            # Find matching close paren
            depth = 1
            j = i + 1
            while j < len(line) and depth > 0:
                if line[j] == '(':
                    depth += 1
                elif line[j] == ')':
                    depth -= 1
                j += 1

            if depth == 0:
                content = line[i+1:j-1]
                if is_latex_math(content):
                    result.append('$')
                    result.append(content)
                    result.append('$')
                    i = j
                    continue

        result.append(line[i])
        i += 1

    return ''.join(result)


def fix_delimiters(input_path: str, output_path: str) -> None:
    """Read input file, fix math delimiters, write to output file."""
    with open(input_path, 'r') as f:
        lines = f.readlines()

    output_lines = []
    in_display_math = False

    for line in lines:
        stripped = line.strip()

        # Display math: standalone [ or ]
        if stripped == '[':
            output_lines.append(line.replace('[', '$$', 1))
            in_display_math = True
        elif stripped == ']':
            output_lines.append(line.replace(']', '$$', 1))
            in_display_math = False
        elif in_display_math:
            # Inside display math - don't convert parentheses
            output_lines.append(line)
        else:
            # Outside display math - convert inline math
            output_lines.append(convert_inline_math(line))

    with open(output_path, 'w') as f:
        f.writelines(output_lines)

    print(f"Converted: {input_path} -> {output_path}")


def main():
    if len(sys.argv) < 2:
        print("Usage: fix_math_delimiters.py <input.md> [output.md]")
        print("       If output not specified, appends '_fixed' before extension")
        sys.exit(1)

    input_path = sys.argv[1]

    if len(sys.argv) >= 3:
        output_path = sys.argv[2]
    else:
        p = Path(input_path)
        output_path = str(p.with_stem(p.stem + '_fixed'))

    fix_delimiters(input_path, output_path)


if __name__ == '__main__':
    main()
