.DEFAULT_GOAL := all.pdf


PANDOC ?= pandoc


PANDOC_FLAGS := \
	--filter pandoc-minted.hs --pdf-engine=xelatex \
	-f markdown+lhs+tex_math_single_backslash -t latex+lhs \
	--top-level-division=chapter


LIDR_FILES := Preface.lidr \
	Basics.lidr \
	Induction.lidr \
	Lists.lidr \
	Poly.lidr \
	Logic.lidr \
	IndProp.lidr \
	Maps.lidr \
	ProofObjects.lidr \
	Rel.lidr \
	Imp.lidr \
	ImpParser.lidr
# TODO: Add more chapters, in order, here.


TEX_FILES := $(LIDR_FILES:.lidr=.tex)


.PHONY: all clean clean-tex


clean: clean-tex
	rm -rf all.* auto _minted-all $(TEX_FILES)


clean-tex: all.tex
	latexmk -pdf -CA all.tex


all.pdf: all.tex
	latexmk -gg -pdf $<


all.tex: book.tex $(TEX_FILES)
	$(PANDOC) $(PANDOC_FLAGS) -N --toc -o $@ \
	$(foreach texfile,$(TEX_FILES),-A $(texfile)) -A footer.tex $<


%.tex: %.lidr
	$(PANDOC) $(PANDOC_FLAGS) -o $@ $<
