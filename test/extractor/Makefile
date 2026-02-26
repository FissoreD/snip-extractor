undefine TEX

SRC=../..
OUT=img
GENERATOR = $(SRC)/extract_code.py

ELPIFILES := $(shell find . -type f -regex ".*\.\(elpi\|v\)")
IGNFILES := $(ELPIFILES:.elpi=.eelpi)
IGNFILES := $(IGNFILES:.v=.ev)

TEXFILES := $(shell find . -type f -regex ".*\.tex")
PDFFILES := $(TEXFILES:.tex=.pdf)
TEX_CMD = pdflatex -synctex=1 -interaction=nonstopmode --shell-escape 

main:
	$(MAKE) generator -j4 && $(MAKE) latex -j4 -k

generator: $(IGNFILES)

latex: $(PDFFILES)

%.eelpi: %.elpi
	mkdir -p $(OUT) && python3 $(GENERATOR) $(OUT) $<
%.ev: %.v
	mkdir -p $(OUT) && python3 $(GENERATOR) $(OUT) $<

%.pdf: %.tex
	cd $(OUT) && $(TEX_CMD) $(notdir $<) && $(TEX_CMD) $(notdir $<)

