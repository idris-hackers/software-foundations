# _[Software Foundations][SF] in Idris_

[![Build Status](https://travis-ci.org/idris-hackers/software-foundations.svg?branch=develop)](https://travis-ci.org/idris-hackers/software-foundations)

:book: [Download the PDF][PDF]


## Building

To rebuild the PDF, ensure the [prerequisites][prereqs] are installed, then:

```fish
make pdf
```


### Prerequisites

Others may work, but here are the versions I'm using.

| Dependency       |                                Version |
|------------------|----------------------------------------|
| [(run)ghc][GHC]  |                                  8.0.2 |
| [Idris][]        |                                  1.1.1 |
| [latexmk][]      |                                  4.52c |
| [Make][]         |                                  4.2.1 |
| [minted][]       |                                  2.4.1 |
| [Monoid][]       |                                   0.61 |
| [Pandoc][]       |                               1.19.2.1 |
| [pandoc-types][] |                               1.17.0.5 |
| [Python][]       |                                  3.6.1 |
| [Pygments][]     |                                  2.2.0 |
| [XeLaTeX][]      | 3.14159265-2.6-0.99998 (TeX Live 2017) |

### Installing prerequisites

- [macOS](prerequisites_macOS.md)

<!-- Named Links -->

[SF]: http://www.cis.upenn.edu/%7Ebcpierce/sf/current/index.html
[PDF]: https://idris-hackers.github.io/software-foundations/pdf/sf-idris-2018.pdf
[prereqs]: #prerequisites
[GHC]: https://www.haskell.org/ghc/
[Idris]: https://www.idris-lang.org
[latexmk]: https://www.ctan.org/pkg/latexmk/
[Make]: https://www.gnu.org/software/make/
[minted]: http://www.ctan.org/pkg/minted
[Monoid]: http://larsenwork.com/monoid/
[Pandoc]: http://pandoc.org
[pandoc-types]: https://github.com/jgm/pandoc-types
[Python]: https://www.python.org
[Pygments]: http://pygments.org
[XeLaTeX]: http://tug.org/xetex/
