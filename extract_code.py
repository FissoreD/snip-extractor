import os, sys, re
import code_wrapper

# Base class for snippet/latex generation.  
# clean_line is not a plain string processor; it must be a callable that
# accepts a **boolean** and returns another function taking a **string**.
# The boolean indicates whether the line to be cleaned is part of a minted
# code environment (i.e. verbatim text).  When `escape` is False the caller
# is outside a verbatim block and extra escaping (e.g. converting `_` to
# `\_`) is required. Passing `escape` through allows subclasses to know the
# context when performing replacements.
class C:
    def __init__(self,oc,ec,od,ext,ot,ct,esc,clean_line):
        self.OPEN_COMMENT = oc
        self.END_COMMENT = ec
        self.OUT_DIR = od
        self.EXTENSION = ext
        self.OPEN_TAG = ot
        self.CLOSE_TAG = ct
        self.escape = esc
        # `clean_line` is called here with the escape flag to produce a
        # per-line cleaning function used throughout the class.
        self.clean_line = clean_line(self.escape)

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


    # def clean_line(self,l):
    #     return clean_line_global(l,self.escape)
        

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
        cnt = code_wrapper.build_cnt(cnt)
        if os.path.exists(fout):
            with open(fout, "r") as fr:
                cnt1 = fr.read()
                if cnt == cnt1:
                    return
        with open(fout, "w") as f:
            f.write(cnt)

class snip(C):
    def __init__(self,open_comment,close_comment,mintag,mintinl,out,ext,clean_line):
        super(snip,self).__init__(open_comment,close_comment,out,ext,"SNIP:","ENDSNIP",True,clean_line)
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
    def __init__(self,mintag,mintinl,out,clean_line):
        super(theorem,self).__init__("(*","*)",out,"v","SNIPT:","ENDSNIPT",True,clean_line)
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
    def __init__(self,out,clean_line):
        super(bussproof,self).__init__("(*","*)",out,"v","prooftree:","endprooftree",False,clean_line)



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
    def clean_line(escape):
        def f(l):
            def esc(l):
                return f"~{l}~" if escape else l
            def m(l) : 
                return f"\\\\ensuremath{{{l}}}"
            l = l.replace("%", "\%")
            if not escape:
                l = re.sub(r'_', '\\_', l)
            return l
        return f

    out = sys.argv[1]
    fname = sys.argv[2]
    bussproof(out,clean_line).read_file(fname)
    if fname.endswith(".v"):
        snip("(*", "*)", "coqcode","cI",out,"v",clean_line).read_file(fname)
        theorem("coqcode","cI",out,clean_line).read_file(fname)
    if fname.endswith(".elpi"):
        snip("%", "", "elpicode","eI",out,"elpi",clean_line).read_file(fname)