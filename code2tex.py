from pathlib import Path
import sys

mint_opt = r"fontsize=\small,autogobble,escapeinside=~~,mathescape=true,frame=leftline,framerule=0pt,framesep=1em"

extension_mapper = {
    ".v": "coq",
    ".elpi": "elpi",
    ".hs": "hs"
}

def max_len(l):
    m = 0
    for i in l:
        m = max(m, len(i))
    return m

def build_cnt(cnt:str):
    cnt_list = cnt.split("\n")
    len = max_len(cnt_list)
    return "\\documentclass[border=2mm, varwidth]{standalone}\n" \
        "\\usepackage{mminted}\n" \
        "\\usepackage{macro}\n" \
        "\\begin{document}\n" \
        f"\\begin{{varwidth}}{{{len+3}\\charwidth}}\n" \
        f"{cnt}\n" \
        "\\end{varwidth}"\
        "\\end{document}"

# excludes all the content before the first occurence of START
# if START is absent then it returns all the document
def clean_cnt(l):
    pos = 0
    for i, e in enumerate(l):
        if "START" in e:
            pos = i
            break
    return l[pos+1:]


def build_file(fname):
    with open(fname) as cnt:
        cnt = cnt.readlines()
        cnt = clean_cnt(cnt)
        path = Path(fname)
        mint_tag = f"{extension_mapper[path.suffix]}code"
        cnt_flat = "".join(cnt)
        cnt = f"\\begin{{{mint_tag}}}\n" \
            f"{cnt_flat}\n" \
            f"\\end{{{mint_tag}}}\n"
        print("CNT IS", cnt)
        cnt = build_cnt(cnt)
        with open(path.stem + ".tex", "w") as fout:
            fout.write(cnt)

if __name__ == "__main__":
    ag = sys.argv[1]
    build_file(ag)

