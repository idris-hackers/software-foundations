.DEFAULT_GOAL := all.pdf


# TODO: Find pandoc executable.
PANDOC    ?= pandoc


PANDOC_FLAGS := \
	--filter pandoc-minted.hs --latex-engine=xelatex \
	-f markdown+lhs+tex_math_single_backslash -t latex+lhs \
	--top-level-division=chapter


LIDRFILES := Preface.lidr \
	Basics.lidr \
	Induction.lidr \
	Lists.lidr \
	Poly.lidr
# TODO: Add more chapters, in order, here.


TEXFILES  := $(LIDRFILES:.lidr=.tex)


.PHONY: all clean


clean: clean-tex
	rm -rf all.* auto _minted-all $(TEXFILES)


clean-tex: all.tex
	latexmk -pdf -CA all.tex


all.pdf: all.tex
	latexmk -pdf $<


all.tex: book.tex $(TEXFILES)
	$(PANDOC) $(PANDOC_FLAGS) -N --toc -o $@ \
	$(foreach texfile,$(TEXFILES),-A $(texfile)) -A footer.tex $<


%.tex: %.lidr
	$(PANDOC) $(PANDOC_FLAGS) -o $@ $<
