---
pandoc-minted:
  language: idris
---

= Basics

> ||| Basics: Functional Programming in Idris
> module Basics
>
> %hide (&&)
> %hide (||)
>
> %access public export
>
> {- REMINDER:
>
> #####################################################
> ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
> #####################################################
>
> (See the [Preface] for why.)
>
> -}

-- TODO: discuss postulate


== Introduction

The functional programming style brings programming closer to simple, everyday
mathematics: If a procedure or method has no side effects, then (ignoring
efficiency) all we need to understand about it is how it maps inputs to outputs
-- that is, we can think of it as just a concrete method for computing a
mathematical function. This is one sense of the word "functional" in "functional
programming." The direct connection between programs and simple mathematical
objects supports both formal correctness proofs and sound informal reasoning
about program behavior.

The other sense in which functional programming is "functional" is that it
emphasizes the use of functions (or methods) as _first-class_ values -- i.e.,
values that can be passed as arguments to other functions, returned as results,
included in data structures, etc. The recognition that functions can be treated
as data in this way enables a host of useful and powerful idioms.

Other common features of functional languages include _algebraic data types_ and
_pattern matching_, which make it easy to construct and manipulate rich data
structures, and sophisticated _polymorphic type systems_ supporting abstraction
and code reuse. Idris shares all of these features.

The first half of this chapter introduces the most essential elements of Idris's
functional programming language. The second half introduces some basic _tactics_
that can be used to prove simple properties of Idris programs.

-- TODO: Edit the following.

One unusual aspect of Coq is that its set of built-in features is _extremely_
small, For example, instead of providing the usual palette of atomic data types
(booleans, integers, strings, etc.), Coq offers a powerl mechanism for defining
new data types from scratch, from which all these familiar types arise as
instances.

Naturally, the Coq distribution comes with an extensive standard library
providing definitions of booleans, numbers, and many common data structures like
lists and hash tables. But there is nothing magic or primitive about these
library definitions. To illustrate this, we will explicitly recapitulate all the
definitions we need in this course, rather than just getting them implicitly
from the library.

To see how this definition mechanism works, let's start with a very simple
example.


== Enumerated Types

=== Days of the Week

The following declaration tells Idris that we are defining a new set of data
values -- a _type_.

> data Day = Monday
>          | Tuesday
>          | Wednesday
>          | Thursday
>          | Friday
>          | Saturday
>          | Sunday

The type is called `Day`, and its members are `Monday`, `Tuesday`, etc. The
right hand side of the definition can be read "`Monday` is a `Day`, `Tuesday` is
a `Day`, etc."

Having defined `Day`, we can write functions that operate on days.

Type the following:

```idris
nextWeekday : Day -> Day
```

Then with point on `nextWeekday`, call \mintinline[]{elisp}{idris-add-clause}
(\mintinline[]{elisp}{M-RET d} in Spacemacs).

```idris
nextWeekday : Day -> Day
nextWeekday x = ?nextWeekday_rhs
```

With the point on `day`, call \mintinline[]{elisp}{idris-case-split}
(\mintinline[]{elisp}{M-RET c} in Spacemacs).

```idris
nextWeekday : Day -> Day
nextWeekday Monday = ?nextWeekday_rhs_1
nextWeekday Tuesday = ?nextWeekday_rhs_2
nextWeekday Wednesday = ?nextWeekday_rhs_3
nextWeekday Thursday = ?nextWeekday_rhs_4
nextWeekday Friday = ?nextWeekday_rhs_5
nextWeekday Saturday = ?nextWeekday_rhs_6
nextWeekday Sunday = ?nextWeekday_rhs_7
```

Fill in the proper `Day` constructors and align whitespace as you like.

> nextWeekday : Day -> Day
> nextWeekday Monday    = Tuesday
> nextWeekday Tuesday   = Wednesday
> nextWeekday Wednesday = Thursday
> nextWeekday Thursday  = Friday
> nextWeekday Friday    = Monday
> nextWeekday Saturday  = Monday
> nextWeekday Sunday    = Monday

Call \mintinline[]{elisp}{idris-load-file} (\mintinline[]{elisp}{M-RET r} in
Spacemacs) to load the `Basics` module with the finished `nextWeekday`
definition.

Having defined a function, we should check that it works on some examples. There
are actually three different .ways to do this in Idris.

First, we can evalute an expression involving `nextWeekday` in a REPL.

```idris
nextWeekday Friday
-- Monday : Day
```

```idris
nextWeekday (nextWeekday Saturday)
-- Tuesday : Day
```

Second, we can record what we _expect_ the result to be in the form of a proof.

> testNextWeekday :
>   (nextWeekday (nextWeekday Saturday)) = Tuesday

This declaration does two things: it makes an assertion (that the second weekday
after `Saturday` is `Tuesday`) and it gives the assertion a name that can be
used to refer to it later.

Having made the assertion, we can also ask Idris to verify it, like this:

> testNextWeekday = Refl

(For simple proofs like this, you can call
\mintinline[]{elisp}{idris-add-clause} (\mintinline[]{elisp}{M-RET d}) with the
point on the name (`testNextWeekday`) in the type signature and then call
\mintinline[]{elisp}{idris-proof-search} (\mintinline[]{elisp}{M-RET p}) with
the point on the resultant hole to have Idris solve the proof for you.)

-- TODO: Edit this

The details are not important for now (we'll come back to them in a bit), but
essentially this can be read as "The assertion we've just made can be proved by
observing that both sides of the equality evaluate to the same thing, after some
simplification."


-- TODO: verify the "main uses" claim.

Third, we can ask Idris to _generate_, from our definition, a program in some
other, more conventional, programming (C, Javascript and Node are bundled with
Idris) with a high-performance compiler. This facility is very interesting,
since it gives us a way to construct _fully certified_ programs in mainstream
languages. Indeed, this is one of the main uses for which Idris was developed.
We'll come back to this topic in later chapters.
