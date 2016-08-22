# _[Software Foundations][SF] in Idris_

:book: [Download the PDF][PDF]


## Usage

To rebuild the PDF, ensure the [prerequisites][prereqs] are installed, then:

```fish
make
```


## Prerequisites

- [Idris](http://www.idris-lang.org)
- [Make](https://www.gnu.org/software/make/)
- [Pandoc](http://pandoc.org)
- [Python](https://www.python.org)
- [Pygments](http://pygments.org)
- [XeLaTeX](http://tug.org/xetex/)
- [minted](http://www.ctan.org/pkg/minted)


Others may work, but here are the versions I'm using:

```fish
$ idris --version
0.12
```

<details>
<summary>`$ make --version`</summary>
```fish
GNU Make 3.81
Copyright (C) 2006  Free Software Foundation, Inc.
This is free software; see the source for copying conditions.
There is NO warranty; not even for MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.

This program built for i386-apple-darwin11.3.0
```
</details>

<details>
<summary>`$ pandoc --version`</summary>
```fish
pandoc 1.17.1
Compiled with texmath 0.8.6.3, highlighting-kate 0.6.2.
Syntax highlighting is supported for the following languages:
    abc, actionscript, ada, agda, apache, asn1, asp, awk, bash, bibtex, boo, c,
    changelog, clojure, cmake, coffee, coldfusion, commonlisp, cpp, cs, css,
    curry, d, diff, djangotemplate, dockerfile, dot, doxygen, doxygenlua, dtd,
    eiffel, elixir, email, erlang, fasm, fortran, fsharp, gcc, glsl,
    gnuassembler, go, hamlet, haskell, haxe, html, idris, ini, isocpp, java,
    javadoc, javascript, json, jsp, julia, kotlin, latex, lex, lilypond,
    literatecurry, literatehaskell, llvm, lua, m4, makefile, mandoc, markdown,
    mathematica, matlab, maxima, mediawiki, metafont, mips, modelines, modula2,
    modula3, monobasic, nasm, noweb, objectivec, objectivecpp, ocaml, octave,
    opencl, pascal, perl, php, pike, postscript, prolog, pure, python, r,
    relaxng, relaxngcompact, rest, rhtml, roff, ruby, rust, scala, scheme, sci,
    sed, sgml, sql, sqlmysql, sqlpostgresql, tcl, tcsh, texinfo, verilog, vhdl,
    xml, xorg, xslt, xul, yacc, yaml, zsh
Default user data directory: /Users/mohacker/.pandoc
Copyright (C) 2006-2016 John MacFarlane
Web:  http://pandoc.org
This is free software; see the source for copying conditions.
There is no warranty, not even for merchantability or fitness
for a particular purpose.
```
</details>

```fish
$ python --version
Python 2.7.10
```

```fish
$ pygmentize -V
Pygments version 2.1.3, (c) 2006-2015 by Georg Brandl.
```

<details>
<summary>`$ xelatex --version`</summary>
```fish
XeTeX 3.14159265-2.6-0.99996 (TeX Live 2016)
kpathsea version 6.2.2
Copyright 2016 SIL International, Jonathan Kew and Khaled Hosny.
There is NO warranty.  Redistribution of this software is
covered by the terms of both the XeTeX copyright and
the Lesser GNU General Public License.
For more information about these matters, see the file
named COPYING and the XeTeX source.
Primary author of XeTeX: Jonathan Kew.
Compiled with ICU version 57.1; using 57.1
Compiled with zlib version 1.2.8; using 1.2.8
Compiled with FreeType2 version 2.6.3; using 2.6.3
Compiled with Graphite2 version 1.3.8; using 1.3.8
Compiled with HarfBuzz version 1.2.6; using 1.2.6
Compiled with libpng version 1.6.21; using 1.6.21
Compiled with poppler version 0.42.0
Using Mac OS X Core Text and Cocoa frameworks
```
</details>


[SF]: http://www.cis.upenn.edu/%7Ebcpierce/sf/current/index.html
[PDF]: https://idris-hackers.github.io/software-foundations/pdf/sf-idris-2016.pdf
[prereqs]: #prerequisites
