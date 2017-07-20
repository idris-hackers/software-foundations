## Contributing

_TBD_ (see [issue #4] for discussion)

### General Workflow

_TODO: write me_


### Formatting

When formatting the [Literate Idris] source, we use [bird tracks] for code meant
to be compiled and a combination of [Markdown] and [LaTeX] for commentary and
illustrative examples that aren't meant to be compiled.

````markdown
= Example

This is some commentary with **bold** and _italicized_ text.

```idris
-- This is an Idris code block which won't be read when compiling the file.
foo : Nat
foo = 42
```


== Code to Compile

The following, however, will be compiled:

> module Example
>
> %access public export
>
> foo : String
> foo = "bar"


== Other Notes

- We can also highlight code inline, e.g. \idr{primes : Inf (List Nat)}.
- To refer to glossary entries, use e.g. \mintinline[]{latex}{\gls{term}}.
````

#### Chapters, Sections, et al.

To denote chapters, sections, and other subdivisions, use `=` as follows:

```markdown
= Chapter
== Section
=== Subsection
==== Subsubsection
```

#### Bold and Italicized Text

We use the succinct Markdown syntax...

```markdown
... to format **bold** and _italicized_ text.
```

#### Lists

We prefer the Markdown syntax here too, e.g.

```markdown
- foo
- bar
- baz
```

#### Code Blocks

Just as with bold and italicized text, we favor the more succinct Markdown
syntax for (fenced) code blocks:

````markdown
```idris
addTwo : Nat -> Nat
addTwo x = x + 2
```
````

For more information, refer to [the relevant GitHub Help document][gfm code blocks].

#### Inline Code

For inline Idris code, use the custom `\mintinline` shortcut `\idr`, e.g.

```tex
To print ``Hello World!'' in Idris, write \idr{putStrLn "Hello, World!"}.
```

For convenience, we've also defined the shortcut `\el` for inline Emacs Lisp
code, e.g.

```latex
Set the value of \el{foo} to \el{42}: \el{(setq foo 42)}.
```

Otherwise, use single backticks for inline monospace text, e.g.

```
This is some `inline monospaced text`.
```

In a certain cases, we might want syntax highlighting for a language other than
Idris or Emacs Lisp. For such cases, use the standard `\mintinline` command,
e.g.

```tex
To declare a theorem in Coq, use \mintinline[]{coq}{Theorem}.
```

#### Glossary

We use the [glossaries package] for defining terms
(in [`src/glossary.tex`][glossary.tex]) and including a glossary in
the [generated PDF][PDF]. See the package documentation for more information,
but here's a quick example:

```tex
What is the \gls{meaning of life}?


\newglossaryentry{meaning of life}{
  description={42}
}
```


### Generating the PDF

To generate the [PDF] we use [Pandoc] and [latexmk]. For more details, check out
the `all.pdf`, `all.tex` and `%.tex` rules in [`src/Makefile`].


<!-- Named Links -->

[issue #4]: https://github.com/idris-hackers/software-foundations/issues/4
[Literate Idris]: http://docs.idris-lang.org/en/latest/tutorial/miscellany.html#literate-programming
[bird tracks]: https://wiki.haskell.org/Literate_programming#Bird_Style
[Markdown]: https://daringfireball.net/projects/markdown/
[LaTeX]: http://www.latex-project.org
[gfm code blocks]: https://help.github.com/articles/creating-and-highlighting-code-blocks/
[glossaries package]: https://www.ctan.org/pkg/glossaries
[glossary.tex]: https://github.com/idris-hackers/software-foundations/blob/master/src/glossary.tex
[`src/Makefile`]: https://github.com/idris-hackers/software-foundations/blob/master/src/glossary.tex
