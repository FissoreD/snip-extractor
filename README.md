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
- [code_wrapper.py](code_wrapper.py): Utility helpers for converting code
  snippets into TeX fragments.

Usage

Both `extract_code.py` and `code_wrapper.py` take an **output directory** as
first argument followed by one input file whose snippets should be
processed. The output folder is created if it does not exist, and the
resulting `.tex` files are written there. You can run them from the command
line directly, for example:

```sh
python3 extract_code.py outdir input2.v
python3 code_wrapper.py outdir input2.v
```

1. Mark snippets in your source file with the designated opening and closing
   tags.
2. Run the extractor to collect snippets and generate LaTeX fragments (see
   above for syntax).
3. Use the generator to assemble standalone `.tex` files ready to compile with
   `pdflatex` (or similar) and `-shell-escape` for `minted`.

Examples of these invocations are also shown in the `Makefile`s under the
`test/` directory; inspect them for concrete command lines that demonstrate
common workflows.

Notes
- The generated LaTeX relies on the `minted` package for syntax highlighting and
  `bussproofs` for derivation/rule presentation.
- You may need to enable `-shell-escape` when compiling the generated `.tex`
  files so `minted` can run Pygments.

If you want a quick example run or help with tags and compilation, open an issue
or ask here.



