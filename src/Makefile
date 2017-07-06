.DEFAULT_GOAL := all.pdf

# TODO: Find pandoc executable.
PANDOC    ?= pandoc

PANDOC_FLAGS := \
	--filter pandoc-minted.hs --latex-engine=xelatex \
	-f markdown+lhs+tex_math_single_backslash -t latex+lhs \
	--top-level-division=chapter

LIDRFILES := Preface.lidr \
	Basics.lidr \
	Induction.lidr
# TODO: Add more chapters, in order, here.

TEXFILES  := $(LIDRFILES:.lidr=.tex)


.PHONY: all clean

clean:
	rm -rf all.{aux,log,out,toc,pdf} _minted-all $(TEXFILES)

all.pdf: all.tex
	latexmk -xelatex -e '$$pdflatex=q/xelatex %O --shell-escape %S/' $<

all.tex: book.tex $(TEXFILES)
	$(PANDOC) $(PANDOC_FLAGS) -N --toc -o $@ \
	$(foreach texfile,$(TEXFILES),-A $(texfile)) $<

%.tex: %.lidr
	$(PANDOC) $(PANDOC_FLAGS) -o $@ $<
