import os, sys, re
from datetime import datetime
import code2tex

def get_file_cnt(lines):
    res = []
    try:
        indexBegin = lines.index("%BEGIN\n")
        indexEnd = lines.index("%END\n")
        res = lines[indexBegin+1:indexEnd]
    finally:
        return res

def print_tex(f,lines, fout, raw = False):
    d1 = os.path.getatime(f)
    d2 = os.path.getatime(fout) if os.path.exists(fout) else 0
    if d1 <= d2 or len(lines) == 0: return
    # print("Generating", fout, datetime.fromtimestamp(d1).strftime("%H:%M:%S"), datetime.fromtimestamp(d2).strftime("%H:%M:%S"))
    lines1 = []
        # if not raw:
            # f.write("\\begin{elpicode}\n")
    for l in lines:
        l = re.sub("^ *% +.*\n","",l)   
        l = re.sub("%~(.*)",r"~\g<1>",l)   
        l = re.sub("^ *%SNIP.*\n","",l)   
        l = re.sub("^ *%ENDSNIP.*\n","",l)   
        l = re.sub("^ *%%%.*\n","",l)   
        l = re.sub("==l",r"~$\\Ue$~",l) 
        l = re.sub("===o",r"~$\\Uo$~",l)
        l = re.sub("==o",r"~$\\Eo$~",l)
        l = re.sub(".*% *HIDE.*\n","",l)
        l = re.sub("% label: (.*).* cnt: (.*)",r"~\\customlabel{\g<1>}{(\g<2>)}~",l)
        l = re.sub("type \(~\$([^ ]+)\$~\) ([^\.]+)",r"~\\PYG{k+kd}{type} \\PYG{n+nf}{(\g<1>)} \\PYG{k+kt}{\g<2>}~",l)
        l = re.sub("type (\([^ ]+\)) ([^\.]+)",r"~\\PYG{k+kd}{type} \\PYG{n+nf}{\g<1>} \\PYG{k+kt}{\g<2>}~",l)
        lines1.append(l)
    # print("Printing", lines1, "into")
    cnt = code2tex.build_cnt(".elpi",lines1)
    if d2 != 0:
        with open(fout, "r") as fr:
            cnt1 = fr.read()
            if cnt == cnt1:
                return
    with open(fout, "w") as fw:
        fw.write(cnt)

def mk_fname(fname):
    return fname.split("/")[-1][:-4] + "tex"

def get_snippets(lines):
    snips = {}
    ingrp = False
    name = ""
    curgrp = []
    for l in lines:
        m = re.match(r"^%ENDSNIP",l)
        if not (m is None):
            snips[name] = curgrp
            ingrp = False
            curgrp = []
        if ingrp is True:
            curgrp = curgrp + [l]
        m = re.match(r"^%SNIP: *(.*) *$",l)
        if not (m is None):
            ingrp = True
            name = m.group(1)
            if name in snips:
                curgrp = snips[name]
            else:
                curgrp = []
    return snips

def read_file(out,fname):
    with open(fname) as f:
        lines = f.readlines()
        # print_tex(fname,get_file_cnt(lines), out + "/" + mk_fname(fname))
        snippets = get_snippets(lines)
        for fname_snip in snippets:
            lines = snippets[fname_snip]
            print_tex(fname,lines, out + "/" +  fname_snip + ".tex")
            # print_tex(fname,lines, out + "/" +  fname_snip + "_raw.tex", True)

        
if __name__ == "__main__":
    out = sys.argv[1]
    fname = sys.argv[2]
    read_file(out,fname)