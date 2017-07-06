PKG   := software_foundations


# TODO: Find idris executable.
IDRIS ?= idris


.PHONY: pdf site


all: pdf site


build:
	$(IDRIS) --build $(PKG).ipkg


pdf:
	$(MAKE) -C src
	mv src/all.pdf docs/pdf/sf-idris-2016.pdf


clean-all: clean clean-docs


clean:
	$(IDRIS) --clean $(PKG).ipkg


clean-docs:
	$(MAKE) -C src clean
	@$(RM) docs/index.html >/dev/null


site: docs/index.html


docs/index.html: README.md
	pandoc -f markdown_github -t html -s -o $@ $<
