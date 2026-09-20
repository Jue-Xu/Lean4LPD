#!/usr/bin/env python3
"""Check that the math of the Markdown documentation renders on GitHub.

GitHub runs Markdown before MathJax on `$...$` and `$$...$$`: backslash-punctuation such as
`\\,` or `\\#` is eaten and `_..._` pairs become emphasis. The documentation therefore writes
inline math as $`...`$ and display math as a ```math fence at column 0 (an indented math fence,
e.g. inside a list item, is not rendered). This script fails on anything else.
Usage: check_md_math.py [FILE ...]   (default: README.md STATEMENTS.md)
"""
import re
import sys

bad = []
for path in sys.argv[1:] or ["README.md", "STATEMENTS.md"]:
    fence = None
    for n, line in enumerate(open(path), 1):
        m = re.match(r"(\s*)```(\w*)", line)
        if m:
            if fence is None and m.group(2) == "math" and m.group(1):
                bad.append((path, n, "indented ```math fence is not rendered"))
            fence = None if fence is not None else m.group(2) or "code"
            continue
        if fence is not None:
            continue
        spans = re.findall(r"\$`[^`\n]+`\$", line)
        if line.lstrip().startswith("|") and any("|" in s for s in spans):
            bad.append((path, n, "'|' inside math in a table row splits the cell"))
        rest = re.sub(r"`[^`\n]*`", "", re.sub(r"\$`[^`\n]+`\$", "", line))
        if "$" in rest:
            bad.append((path, n, "bare '$': write inline math as $`...`$ and display math as a ```math fence"))

for path, n, msg in bad:
    print(f"{path}:{n}: {msg}")
sys.exit(1 if bad else 0)
