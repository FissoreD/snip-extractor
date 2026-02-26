This repository contains Python scripts to extract code snippets from input
files and produce standalone LaTeX files.

Overview
- The tools parse a source file for explicit opening and closing tags that mark
  the start and end of a snippet. These tags allow the Python parser to
  determine snippet boundaries precisely.
- The extraction produces LaTeX output that includes syntax-highlighted code
  using the `minted` package and derivation rules typeset with the `bussproofs`
  package.

Included scripts
- [extract_code.py](extract_code.py): Extract snippets from a source file using
  the tag markers.
- [generate_tex.py](generate_tex.py): Generate standalone LaTeX documents from
  extracted snippets (uses `minted` and `bussproofs`).
- [code2tex.py](code2tex.py): Utility helpers for converting code snippets into
  TeX fragments.

Usage
1. Mark snippets in your source file with the designated opening and closing
   tags.
2. Run the extractor to collect snippets and generate LaTeX fragments.
3. Use the generator to assemble standalone `.tex` files ready to compile with
   `pdflatex` (or similar) and `-shell-escape` for `minted`.

Notes
- The generated LaTeX relies on the `minted` package for syntax highlighting and
  `bussproofs` for derivation/rule presentation.
- You may need to enable `-shell-escape` when compiling the generated `.tex`
  files so `minted` can run Pygments.

If you want a quick example run or help with tags and compilation, open an issue
or ask here.

