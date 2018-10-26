PKG    := software_foundations
PREFIX ?= docs
IDRIS  ?= idris
PDF    ?= sf-idris-2018.pdf


.PHONY: pdf site


all: check pdf site


build:
	$(IDRIS) --build $(PKG).ipkg


check:
	$(IDRIS) --checkpkg $(PKG).ipkg


pdf:
	$(MAKE) -C src
	mv src/all.pdf docs/pdf/${PDF}


clean-all: clean clean-docs


clean:
	$(IDRIS) --clean $(PKG).ipkg


clean-docs:
	$(MAKE) -C src clean
	@$(RM) docs/index.html >/dev/null


site: docs/index.html


docs/index.html: README.md CONTRIBUTING.md
	pandoc -f gfm -t gfm -A CONTRIBUTING.md $< | \
		pandoc -M title='Software Foundations in Idris' \
			-f gfm -t html -s -o $@


install:
	install -m644 -Dt "${PREFIX}" docs/pdf/${PDF}
