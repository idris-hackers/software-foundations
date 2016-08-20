---
pandoc-minted:
  language: idris
---

= Induction: Proof by Induction

First, we import all of our definitions from the previous chapter.

> import Basics

For `import Basics` to work, you first need to use `idris` to compile
`Basics.lidr` into `Basics.ibc`. This is like making a .class file from a .java
file, or a .o file from a .c file. There are at least two ways to do it:

  - In your editor with an Idris plugin, e.g. [Emacs][idris-mode]:

    Open `Basics.lidr`. Evaluate `idris-load-file`.

    There exists similar support for [Vim][idris-vim] and [Sublime
    Text][idris-sublime] as well.

    [idris-mode]: https://github.com/idris-hackers/idris-mode
    [idris-vim]: https://github.com/idris-hackers/idris-vim
    [idris-sublime]: https://github.com/idris-hackers/idris-sublime

  - From the command line:

    Run \mintinline[]{sh}{idris --check --total --noprelude src/Basics.lidr}.

    Refer to the Idris man page (or \mintinline[]{sh}{idris --help} for
    descriptions of the flags.
