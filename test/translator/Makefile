TEXFILES := $(shell find . -type f -regex ".*\.\(elpi\|v\|hs\)")
PDFFILES := $(TEXFILES:.elpi=.tex)
PDFFILES := $(PDFFILES:.v=.tex)
PDFFILES := $(PDFFILES:.hs=.tex)
GENERATOR := ../../code_wrapper.py
TEX_CMD = pdflatex -synctex=1 -interaction=nonstopmode --shell-escape 

img: $(PDFFILES)

%.tex: %.elpi
	(python3 $(GENERATOR) $<) && $(TEX_CMD) $@ && $(TEX_CMD) $@

%.tex: %.v
	(python3 $(GENERATOR) $<) && $(TEX_CMD) $@ && $(TEX_CMD) $@

%.tex: %.hs
	(python3 $(GENERATOR) $<) && $(TEX_CMD) $@ && $(TEX_CMD) $@
