PKG    := software_foundations
PREFIX ?= docs
IDRIS  ?= idris
PDF    ?= sf-idris-2018.pdf


.PHONY: pdf site


all: pdf site


build:
	$(IDRIS) --build $(PKG).ipkg


check:
	$(IDRIS) --checkpkg $(PKG).ipkg


pdf:
	$(MAKE) -C src
	mkdir -p ${PREFIX}/pdf
	mv src/all.pdf ${PREFIX}/pdf/${PDF}


clean-all: clean clean-docs


clean:
	$(IDRIS) --clean $(PKG).ipkg


clean-docs:
	$(MAKE) -C src clean
	@$(RM) ${PREFIX}/index.html >/dev/null


site: ${PREFIX}/index.html


${PREFIX}/index.html: README.md CONTRIBUTING.md
	pandoc -f gfm -t gfm -A CONTRIBUTING.md $< | \
		pandoc -M title='Software Foundations in Idris' \
			-f gfm -t html -s -o $@
