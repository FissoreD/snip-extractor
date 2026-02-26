import os, sys, re

def find_close_par(l, i):
    cnt = 1
    for i in range(i+1,len(l)):
        c = l[i]
        if c == ")": cnt -=1
        elif c == "(": cnt += 1
        if cnt == 0: return i
    return -1

def remove_some_par(l):
    s = "(Some"
    if s not in l: return l
    p = l.index(s)
    cl = find_close_par(l, p)
    if cl > p:
        l = l[:p] + "s" + l[p+2:cl] + l[cl+1:]
        return remove_some_par(l)
    else:
        raise Exception("ERROR")

def clean_line_global(l,escape):
    # if you want to replace with math notation, prefix the string with a call to m
    # if you need to escape minted mode, call esc 
    def esc(l):
        return f"~{l}~" if escape else l
    def m(l) : 
        return f"\\\\ensuremath{{{l}}}"
    l = remove_some_par(l)
    l = l.replace("%G", "")
    l = re.sub(r'\b_\w+\b', '_', l)
    if not escape:
        l = re.sub(r'_', '\\_', l)
    l = re.sub(r'#', esc(m('\\\\#')), l)
    l = re.sub(r'\+\+', esc('\\\\mappend'), l)
    l = re.sub(r'\[::\]', esc('\\\\mnil'), l)
    l = re.sub("Sigma", esc(m("\\\\Sigma")), l)
    # l = re.sub("tree", esc("\\tau"), l)
    l = re.sub("empty", esc(m("\\\\epsilon")), l)
    l = re.sub("fvS", esc(m("\\\\FV")), l)
    l = re.sub("bool", esc(m("\\\\mathbb{B}")), l)
    l = re.sub("program", esc(m("\\\\mathbb{P}")), l)
    l = re.sub("<->", esc(m("\\\\leftrightarrow")), l)
    l = re.sub("->", esc(m("\\\\to")), l)
    l = re.sub("=>", esc(m("\\\\Rightarrow")), l)
    l = re.sub("/\\\\", esc(m("\\\\land")), l)
    # l = re.sub(":=", esc(m("\\\\coloneq")), l)
    l = re.sub("forall", esc(m("\\\\forall")), l)
    l = re.sub("exists", esc(m("\\\\exists")), l)
    l = re.sub("None", esc(m("\\\\square")), l)
    l = re.sub(r"\bmkR\b", "", l)
    # l = re.sub(r"\bA\b", "Atom", l)
    l = re.sub(r"\bseq\b", "list", l)
    l = re.sub(r"\bpath_atom\b", "incomplete", l)
    l = re.sub(r"\bget_subst\b", "next_subst", l)
    l = re.sub(r"\bpath_end\b", "next_tree", l)
    l = re.sub(r"\bget_end\b", "next", l)
    l = re.sub(r"\bTA\b", "Todo", l)
    l = re.sub(r"`<=`", esc(m("\\\\subseteq")), l)
    l = re.sub(r"∨", esc(m("\\\\lor")), l)
    l = re.sub(r"∧", esc(m("\\\\land")), l)
    if escape:
        l = re.sub("some *", esc("\\\\msome"), l)
        l = re.sub("Some *", esc("\\\\msome"), l)
    else:
        l = re.sub("Some", esc("\\\\msome"), l)
        l = re.sub("some", esc("\\\\msome"), l)
    l = re.sub("true", esc(m("\\\\top")), l)
    l = re.sub("false", esc(m("\\\\bot")), l)
    l = l.replace("\bsm\b", " " + esc(m("s_m")) + " ")
    pat = ["v","b","t","r","a", "g", "l"]

    def clean_esc(l):
        m = l.group(1)
        return  "\\ensuremath{\\phantom{!}_{\!\!" + m.replace("~", "").replace("$","") + "}}"


    def change_vars(vn, gl, l):
        return re.sub(f"\\b{vn}('+)|\\b{vn}\\b", esc(m(f"{gl}\g<1>")), l)
    def it_pat(pat,gl,l):
        l = change_vars(pat, gl, l)
        for i in range(10):
            l = change_vars(f"{pat}{i}", f"{gl}_{i}", l)
        return l
    l = it_pat("s", "\\\\sigma", l)
    for p in pat:
        l = it_pat(p, p, l)
        
    l = l.replace("step_tag", "tag") # FIXME
    l = re.sub("\\\\/", esc(m("\\\\lor")), l)
    # l = re.sub("-sub", esc(m("x\\_")), l)
    l = re.sub(r' -sub\(([^)]*)\)', lambda x: esc(clean_esc(x)), l)
    return l

class C:
    def __init__(self,oc,ec,od,ext,ot,ct,esc):
        self.OPEN_COMMENT = oc
        self.END_COMMENT = ec
        self.OUT_DIR = od
        self.EXTENSION = ext
        self.OPEN_TAG = ot
        self.CLOSE_TAG = ct
        self.escape = esc

    def get_file_cnt(self,lines):
        res = []
        try:
            indexBegin = lines.index(f"{self.OPEN_COMMENT}BEGIN{self.END_COMMENT}\n")
            indexEnd = lines.index(f"{self.fOPEN_COMMENT}END{self.END_COMMENT}\n")
            res = lines[indexBegin+1:indexEnd]
        finally:
            return res
        
    def clean_comment(self,l):
        # COMMENT
        return re.sub(fr"^ *{re.escape(self.OPEN_COMMENT)}.*\n","",l)


    def clean_line(self,l):
        return clean_line_global(l,self.escape)
        

    def mk_fname(self,fname):
        return fname.split("/")[-1][:-(len(self.EXTENTION))] + "tex"

    def get_snippets(self, lines):
        snips = {}
        cursnips = []
        curnames = []
        # invariant the length of cursnips and curnames is the same
        for l in lines:
            m = re.match(rf"^ *{re.escape(self.OPEN_COMMENT)}{self.OPEN_TAG} *(.*) *{re.escape(self.END_COMMENT)}$",l)
            if m is not None:
                # entering a new snip
                name = m.group(1).strip()
                curnames.append(name)
                # if we open again a closed snippet we add the content to the previous snip
                cursnips.append(cursnips[name] if name in cursnips else [])
            else:
                m = re.match(rf"^ *{re.escape(self.OPEN_COMMENT)}{self.CLOSE_TAG}",l)
                if m is None:
                    # we are not exiting, we add the new line l to all current snips
                    # note that if cursnips is the empty list nothing is done
                    for x in cursnips:
                        x.append(l)
                else:
                    # we are exiting a snippet, by default we close the 
                    if len(cursnips)>0:
                        snips[curnames.pop()] = cursnips.pop()
        return snips

    def read_file(self,fname):
        with open(fname) as f:
            lines = f.readlines()
            snippets = self.get_snippets(lines)
            for (fname,lines) in snippets.items():
                self.print_tex(lines, fname + ".tex")

    def print_tex(lines, fout, raw = False):
        raise Exception("TO BE IMPLEMENTED IN CHILD")

    def write(self,fout,cnt):
        if not os.path.exists(self.OUT_DIR):
            os.makedirs(self.OUT_DIR)
        fout = f"{self.OUT_DIR}/{fout}"
        if os.path.exists(fout):
            with open(fout, "r") as fr:
                cnt1 = fr.read()
                if cnt == cnt1:
                    return
        with open(fout, "w") as f:
            f.write(cnt)

class snip(C):
    def __init__(self,mintag,mintinl,out):
        super(snip,self).__init__("(*","*)",out,"v","SNIP:","ENDSNIP",True)
        self.MINT_TAG = mintag
        self.MINT_INLINE = mintinl

    def print_tex(self,lines, fout, raw = False):
        if lines == []: return
        cnt = ""
        if len(lines) == 1:
            l = self.clean_line(lines[0].strip())
            l = l[:-2] if l.endswith(":=") else l
            cnt= f"\{self.MINT_INLINE}{{{l}}}"
        else:
            if not raw:
                cnt += (f"\\begin{{{self.MINT_TAG}}}\n")
            for l in lines:
                cnt += self.clean_line(self.clean_comment(l))
            if not raw:
                cnt += f"\\end{{{self.MINT_TAG}}}\n"
        super().write(fout,cnt)

"""
It takes a text on several lines.
The first MUST be of the for "<TAG> th_name:"
    where <TAG> is a identifier like Theorem, Lemma or Axiom.
    th_name is the name of symbol being created.
    the semicolon should be attached to th_name
All the variables in the definition should be quantified with a forall.
It displaies a mintinline if the definition is of exactely one line,
otherwise it displaies a minted multiline code-block
"""
class theorem(C):
    def __init__(self,mintag,mintinl,out):
        super(theorem,self).__init__("(*","*)",out,"v","SNIPT:","ENDSNIPT",True)
        self.MINT_TAG = mintag
        self.MINT_INLINE = mintinl

    def th_name(self, l : str):
        l = l.strip()
        if l.endswith(":"):
            l = l[:-1]
        elif l.endswith(":="):
            l = l[:-2]
        else:
            print(f"error in parsing {l}")
            assert(False)
        ls = l.split()
        assert(ls[0] in ["Theorem", "Lemma", "Axiom", "Definition"])
        name = ls[1]
        if len(l) > 2:
            args = ls [2:]
        else:
            args = []
        return ls[0].lower(), name, args

    def print_tex(self,lines, fout, raw = False):
        if lines == []: return
        cnt = ""
        (env,name,args), tl = self.th_name(lines[0]), lines[1:]
        n1 = name.replace('_', '\_')
        n2 = name.replace('_', '')
        args = "" if len(args) == 0 else (f" \\{self.MINT_INLINE}{{" + self.clean_line(" ".join(args)) + "}")
        cnt += f"\\begin{{{env}}}[{n1}{args}]\label{{th:{n2}}}"
        if len(tl) > 0:
            txt = self.clean_line(tl[0].strip())
            cnt += f"\\{self.MINT_INLINE}{{{txt}}}"
            tl = tl[1:]
        if len(tl) != 0:
            cnt += f"~\n\\begin{{{self.MINT_TAG}}}\n"
            for l in tl:
                cnt += self.clean_line(self.clean_comment(l))
            cnt += f"\\end{{{self.MINT_TAG}}}\n"
        cnt += f"\end{{{env}}}"
        
        super().write(fout,cnt)


def flatten(xss):
    return [x for xs in xss for x in xs]

# Returns the bussproof representation of an inductive:
# it does not work for:
# inductive with hypothesis containing arrows
# mutual recursive inductives

def stack_anchor(f1,f2):
    return f"\stackanchor{{{f1}}}{{{f2}}}"
class bussproof(C):
    def __init__(self,out):
        super(bussproof,self).__init__("(*","*)",out,"v","prooftree:","endprooftree",False)



    def print_bp(self,name,hyps,concl):
        lines = ["\\begin{prooftree}"]
        # reset hyps if too many or too few
        if len(hyps) == 4:
            x = []
            for i in range (len(hyps)//2):
                x.append(stack_anchor(hyps[2*i], hyps[2*i+1]))
            hyps = x
            

        for s in hyps:
            lines.append(f"  \\AxiomC{{{(s)}}}")

        n = len(hyps)            

        if n == 0:
            n = 1
            lines.append("  \\AxiomC{\phantom{A}}")

        lines.append(f"  \\RightLabel{{\\textit{{{(name)}}}}}")

        L = ["Unary","Binary","Trinary"]

        if n > len(L):
            print(hyps)
            raise ValueError("Too many premises for bussproofs")
        else:
            tag = L[n-1]

        lines.append(f"  \\{tag}InfC{{{(concl)}}}")

        lines.append("\\end{prooftree}")
        return "\n".join(lines)

    def clean_line(self, l):
        # l = l.replace("_","\_")
        # l = l.replace("&","\&")
        return super().clean_line(l)
    
    def split_hyps(self,hyps):
        hyps = hyps.split("->")
        hyps = [self.clean_line(i) for i in hyps]
        return hyps

    def parse_inductive (self,l):
        l = l.split(":",1)
        # print("LINES:= ", l)
        cname = self.clean_line(l[0].split(maxsplit=1)[0])
        hyps = flatten([self.split_hyps(i) for i in l[1:]])
        return self.print_bp(cname, hyps[:-1],hyps[-1])

    # each constructor should be on a new line
    def print_tex(self,lines, fout, raw = False):
        for (i,e) in enumerate(lines):
            lines[i] = self.clean_comment(e).replace("\n","").strip().strip(".")
            
        lines = "".join(lines)
        lines = re.split(r'(?<!\|)\|(?!\|)', lines)
        cnt = ""
        for i in lines[1:]:
            cnt += "\n"+self.parse_inductive(i)
        super().write(fout,cnt)

if __name__ == "__main__":
    out = sys.argv[1]
    fname = sys.argv[2]
    bussproof(out).read_file(fname)
    snip("coqcode","cI",out).read_file(fname)
    theorem("coqcode","cI",out).read_file(fname)