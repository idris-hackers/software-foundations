all:
	$(MAKE) -C src all
	$(MAKE) -C src all.pdf
	mv src/all.pdf docs/pdf/sf-idris-2016.pdf

clean:
	$(MAKE) -C src clean
