.DEFAULT_GOAL := all

# TODO: Find pandoc executable.
PANDOC    ?= pandoc

LIDRFILES := Preface.lidr \
	Basics.lidr \
	Induction.lidr
# TODO: Add more chapters, in order, here.

TEXFILES  := $(LIDRFILES:.lidr=.tex)

.PHONY: clean

all: all.pdf

clean:
	rm -rf all.{aux,log,out,toc,pdf} _minted-all $(TEXFILES)

all.pdf: all.tex
	xelatex -shell-escape $<
	xelatex -shell-escape $<

all.tex: book.tex $(TEXFILES)
	$(PANDOC) --filter pandoc-minted.py --latex-engine=xelatex \
	-f markdown+lhs+tex_math_single_backslash -t latex+lhs \
	--chapters -N \
	--toc \
	-o $@ $(foreach tex,$(filter-out $<,$^),-A $(tex)) \
	book.tex

%.tex: %.lidr
	$(PANDOC) --filter pandoc-minted.py --latex-engine=xelatex \
	-f markdown+lhs+tex_math_single_backslash -t latex+lhs \
	--chapters -N \
	-o $@ $<
