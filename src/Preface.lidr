= Preface

== Welcome

This is the entry point in a series of electronic textbooks on various aspects
of _Software Foundations_ --- the mathematical underpinnings of reliable
software. Topics in the series include basic concepts of logic,
computer-assisted theorem proving, the Coq proof assistant, functional
programming, operational semantics, logics for reasoning about programs, and
static type systems. The exposition is intended for a broad range of readers,
from advanced undergraduates to PhD students and researchers. No specific
background in logic or programming languages is assumed, though a degree of
mathematical maturity will be helpful.

The principal novelty of the series is that it is one hundred percent formalized
and machine-checked: each text is literally a script for Idris. The books are
intended to be read alongside (or inside) an interactive session with Idris. All
the details in the text are fully formalized in Idris, and most of the exercises
are designed to be worked using Idris.

The files in each book are organized into a sequence of core chapters, covering
about one semester's worth of material and organized into a coherent linear
narrative, plus a number of "offshoot" chapters covering additional topics. All
the core chapters are suitable for both upper-level undergraduate and graduate
students.

This book, _Logical Foundations_, lays groundwork for the others, introducing
the reader to the basic ideas of functional programming, constructive logic, and
the Idris programming language.


== Overview

Building reliable software is really hard. The scale and complexity of modern
systems, the number of people involved, and the range of demands placed on them
make it extremely difficult to build software that is even more-or-less correct,
much less 100% correct. At the same time, the increasing degree to which
information processing is woven into every aspect of society greatly amplifies
the cost of bugs and insecurities.

Computer scientists and software engineers have responded to these challenges by
developing a whole host of techniques for improving software reliability,
ranging from recommendations about managing software projects teams (e.g.,
extreme programming) to design philosophies for libraries (e.g.,
model-view-controller, publish-subscribe, etc.) and programming languages (e.g.,
object-oriented programming, aspect-oriented programming, functional
programming, ...) to mathematical techniques for specifying and reasoning about
properties of software and tools for helping validate these properties. The
_Software Foundations_ series is focused on this last set of techniques.
developing a whole host of techniques for improving software reliability,
ranging from recommendations about managing software projects and organizing
programming teams (e.g., extreme programming) to design philosophies for
libraries (e.g., model-view-controller, publish-subscribe, etc.) and programming
languages (e.g., object-oriented programming, aspect-oriented programming,
functional programming, ...) to mathematical techniques for specifying and
reasoning about properties of software and tools for helping validate these
properties.

The text is constructed around three conceptual threads:

1. basic tools from \gls{logic} for making and justifying precise claims about
   programs;

2. the use of \glspl{proof assistant} to construct rigorous logical arguments;

3. \gls{functional programming}, both as a method of programming that simplifies
   reasoning about programs and as a bridge between programming and logic;

Some suggestions for further reading can be found in the
\todo{nameref}Postscript chapter.

<!-- Bibliographic information for all cited works can be found in the file Bib. -->
\todo[inline]{write a bibliography}


=== Logic

Logic is the field of study whose subject matter is \glspl{proof} ---
unassailable arguments for the truth of particular propositions.  Volumes have
been written about the central role of logic in computer science. Manna and
Waldinger called it "the calculus of computer science," while Halpern et al.'s
paper _On the Unusual Effectiveness of Logic in Computer Science_ catalogs
scores of ways in which logic offers critical tools and insights. Indeed, they
observe that "As a matter of fact, logic has turned out to be significantly more
effective in computer science than it has been in mathematics. This is quite
remarkable, especially since much of the impetus for the development of logic
during the past one hundred years came from mathematics."

In particular, the fundamental tools of \glspl{inductive proof} are ubiquitous
in all of computer science. You have surely seen them before, perhaps in a
course on discrete math or analysis of algorithms, but in this course we will
examine them more deeply than you have probably done so far.


=== Proof Assistants

The flow of ideas between logic and computer science has not been
unidirectional: CS has also made important contributions to logic. One of these
has been the development of software tools for helping construct \glspl{proof}
of logical propositions. These tools fall into two broad categories:

  - \Glspl{automated theorem prover} provide "push-button" operation: you give
    them a proposition and they return either _true_, _false_, (or sometimes,
    _don't know:_ran out of time_). Although their capabilities are still
    limited to specific domains, they have matured tremendously in recent years
    and are used now in a multitude of settings. Examples of such tools include
    SAT solvers, SMT solvers, and model checkers.

  - \Glspl{proof assistant} are hybrid tools that automate the more routine
    aspects of building \glspl{proof} while depending on human guidance for more
    difficult aspects. Widely used \glspl{proof assistant} include Isabelle,
    Agda, Twelf, ACL2, PVS, Coq, and Idris, among many others.

This course is based around Idris, a general purpose pure \gls{functional
programming} language with glspl{dependent type} that has been under development
since 2006 and that in recent years has attracted a community of users in both
research and hobby. Idris provides a rich environment for interactive
development of machine-checked formal reasoning. The kernel of the Idris system
is full \glspl{dependent type} with \gls{dependent pattern matching}, which
allows \glspl{type} to be predicated on \glspl{value}, enabling some aspects of
a program's behavior to be specified precisely in the \gls{type}. On top of this
kernel, the Idris environment provides high-level facilities for \gls{proof}
development, including powerful \glspl{elaboration reflection} for constructing
complex \glspl{proof} semi-automatically, and special-purpose programming
language for defining new proof-automation tactics for specific situations.

By the way, in case you're wondering about the name, here's what
\href{http://docs.idris-lang.org/en/latest/faq/faq.html}{the official Idris FAQ}
says: "British people of a certain age may be familiar with this
\href{https://www.youtube.com/watch?v=G5ZMNyscPcg}{singing dragon}. If that
doesn’t help, maybe you can invent a suitable acronym :-) ."


=== Functional Programming

The term \gls{functional programming} refers both to a collection of programming
idioms that can be used in almost any programming language and to a family of
programming languages designed to emphasize these idioms, including Haskell,
OCaml, Standard ML, F$^\sharp$, Scala, Scheme, Racket, Common Lisp, Clojure,
Erlang, Coq, and Idris.

\Gls{functional programming} has been developed over many decades --- indeed,
its roots go back to Church's lambda-calculus, which was invented in the 1930s,
well before the first computers (at least the first electronic ones)! But since
the early '90s it has enjoyed a surge of interest among industrial engineers and
language designers, playing a key role in high-value systems at companies like
Jane St. Capital, Microsoft, Facebook, and Ericsson.

The most basic tenet of \gls{functional programming} is that, as much as
possible, computation should be \gls{pure}, in the sense that the only effect of
execution should be to produce a result: it should be free from \glspl{side
effect} such as I/O, assignments to mutable variables, redirecting pointers,
etc. For example, whereas an \gls{imperative} sorting function might take a list
of numbers and rearrange its pointers to put the list in order, a pure sorting
function would take the original list and return a _new_ list containing the
same numbers in sorted order.

A significant benefit of this style of programming is that it makes programs
easier to understand and reason about. If every operation on a data structure
yields a new data structure, leaving the old one intact, then there is no need
to worry about how that structure is being shared and whether a change by one
part of the program might break an invariant that another part of the program
relies on. These considerations are particularly critical in concurrent systems,
where every piece of mutable state that is shared between threads is a potential
source of pernicious bugs. Indeed, a large part of the recent interest in
functional programming in industry is due to its simpler behavior in the
presence of concurrency.

Another reason for the current excitement about functional programming is
related to the first: functional programs are often much easier to parallelize
than their imperative counterparts. If running a computation has no effect other
than producing a result, then it does not matter _where_ it is run. Similarly,
if a data structure is never modified destructively, then it can be copied
freely, across cores or across the network. Indeed, the "Map-Reduce" idiom,
which lies at the heart of massively distributed query processors like Hadoop
and is used by Google to index the entire web is a classic example of functional
programming.

For purposes of this course, functional programming has yet another significant
attraction: it serves as a bridge between logic and computer science. Indeed,
Idris itself can be viewed as a combination of a small but extremely expressive
functional programming language plus a set of tools for stating and proving
logical assertions. Moreover, when we come to look more closely, we find that
these two sides of Idris are actually aspects of the very same underlying
machinery --- i.e., _\glspl{proof} are programs_.


=== Further Reading

This text is intended to be self contained, but readers looking for a deeper
treatment of particular topics will find some suggestions for further reading in
the \todo{nameref}Postscript chapter.


== Practicalities

=== Chapter Dependencies

\todo[inline]{Copy/recreate deps.html}

A diagram of the dependencies between chapters and some suggested
paths through the material can be found in the file `deps.html`.
\todo{Link deps.html}


=== System Requirements

Idris runs on Windows, Linux, and macOS.  You will need:

  - A current installation of Idris, available from
    \href{https://www.idris-lang.org/}{the Idris home page}. Everything should
    work with version 1.3.0. (Other versions may work, but haven't been tested
    by the Idris translation maintainers.)

  - A supported editor for interacting with Idris. Currently, there are (at
    least) five choices:

      - \href{https://github.com/idris-hackers/atom-language-idris}{atom-language-idris}:
        An Idris Mode for Atom.io

      - \href{https://github.com/idris-hackers/idris-mode}{idris-mode}:
        Idris syntax highlighting, compiler-supported editing, interactive REPL
        and more things for Emacs

      - \href{https://github.com/idris-hackers/idris-sublime}{idris-sublime}:
        A Plugin to use Idris with Sublime

      - \href{https://github.com/idris-hackers/idris-vim}{idris-vim}:
        Idris mode for vim

      - \href{https://github.com/zjhmale/vscode-idris}{idris-vscode}:
        Idris for Visual Studio Code
        \url{https://marketplace.visualstudio.com/items?itemName=zjhmale.Idris}


=== Exercises

Each chapter includes numerous exercises. Each is marked with a "star rating,"
which can be interpreted as follows:

  - One star: easy exercises that underscore points in the text and that, for
    most readers, should take only a minute or two. Get in the habit of working
    these as you reach them.

  - Two stars: straightforward exercises (five or ten minutes).

  - Three stars: exercises requiring a bit of thought (ten minutes to half an
    hour).

  - Four and five stars: more difficult exercises (half an hour and up).

lso, some exercises are marked "advanced," and some are marked "optional." Doing
just the non-optional, non-advanced exercises should provide good coverage of
the core material. Optional exercises provide a bit of extra practice with key
concepts and introduce secondary themes that may be of interest to some
readers. Advanced exercises are for readers who want an extra challenge and a
deeper cut at the material.

*Please do not post solutions to the exercises in a public place.* Software
Foundations is widely used both for self-study and for university
courses. Having solutions easily available makes it much less useful for
courses, which typically have graded homework assignments. We especially request
that readers not post solutions to the exercises anyplace where they can be
found by search engines.


=== Downloading the Idris Files

\todo[inline]{See
\href{https://github.com/idris-hackers/software-foundations/issues/25}{\#25} and
\href{https://github.com/idris-hackers/software-foundations/issues/30}{\#30}}

\todo[inline]{Generate a "release" after the Rel chapter and update this
subsection accordingly.}

A tar file containing the full sources for the "release version" of these notes
(as a collection of Literate Idris files) is available here:

\url{https://github.com/idris-hackers/software-foundations/releases}

(If you are using the book as part of a class, your professor may give you
access to a locally modified version of the files, which you should use instead
of the release version.)
