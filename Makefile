all: pdf site

pdf:
	$(MAKE) -C src all
	$(MAKE) -C src all.pdf
	mv src/all.pdf docs/pdf/sf-idris-2016.pdf

clean:
	$(MAKE) -C src clean
	@$(RM) docs/index.html >/dev/null

site: docs/index.html

docs/index.html: README.md
	pandoc -f markdown_github -t html -s -o $@ $<
