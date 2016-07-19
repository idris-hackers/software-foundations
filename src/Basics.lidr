---
pandoc-minted:
  language: idris
---

= Basics

**REMINDER**:

             #####################################################
             ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
             #####################################################

                           (See the Preface for why.)

> ||| Basics: Functional Programming in Idris
> module Basics
>
> import Prelude.Interfaces
> import Prelude.Nat
>
> %access public export
>
> %default total


`postulate` is Idris's "escape hatch" that says accept this definition without
proof. We use it to mark the 'holes' in the development that should be completed
as part of your homework exercises. In practice, `postulate` is useful when
you're incrementally developing large proofs.


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


== Enumerated Types

\color{red}
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
\color{black}

To see how this definition mechanism works, let's start with a very simple
example.


=== Days of the Week

The following declaration tells Idris that we are defining a new set of data
values -- a _type_.

> namespace Days
>
>   ||| Days of the week.
>   data Day =
>            ||| `Monday` is a `Day`.
>            Monday |
>            ||| `Tuesday` is a `Day`.
>            Tuesday |
>            ||| `Wednesday` is a `Day`.
>            Wednesday |
>            ||| `Thursday` is a `Day`.
>            Thursday |
>            ||| `Friday` is a `Day`.
>            Friday |
>            ||| `Saturday` is a `Day`.
>            Saturday |
>            ||| `Sunday` is a `Day`.
>            Sunday

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

>   ||| Determine the next weekday after a day.
>   nextWeekday : Day -> Day
>   nextWeekday Monday    = Tuesday
>   nextWeekday Tuesday   = Wednesday
>   nextWeekday Wednesday = Thursday
>   nextWeekday Thursday  = Friday
>   nextWeekday Friday    = Monday
>   nextWeekday Saturday  = Monday
>   nextWeekday Sunday    = Monday

Call \mintinline[]{elisp}{idris-load-file} (\mintinline[]{elisp}{M-RET r} in
Spacemacs) to load the `Basics` module with the finished `nextWeekday`
definition.

\color{red}
-- TODO: Verify that top-level type signatures are optional.

One thing to note is that the argument and return types of this function are
explicitly declared. Like most functional programming languages, Idris can often
figure out these types for itself when they are not given explicitly -- i.e., it
performs _type inference_ -- but we'll include them to make reading easier.
\color{black}

Having defined a function, we should check that it works on some examples. There
are actually three different .ways to do this in Idris.

First, we can evalute an expression involving `nextWeekday` in a REPL.

```idris
λΠ> nextWeekday Friday
-- Monday : Day
```

```idris
λΠ> nextWeekday (nextWeekday Saturday)
-- Tuesday : Day
```

\color{red}
-- TODO: Mention other editors? Discuss idris-mode?
\color{black}

We show Idris's responses in comments, but, if you have a computer handy, this
would be an excellent moment to fire up the Idris interpreter under your
favorite Idiris-friendly text editor -- such as Emacs or Vim -- and try this for
and try this for yourself. Load this file, `Basics.lidr` from the book's
accompanying Idris sources, find the above example, submit it to the Idris REPL,
and observe the result.

Second, we can record what we _expect_ the result to be in the form of a proof.

>   ||| The second weekday after `Saturday` is `Tuesday`.
>   testNextWeekday :
>     (nextWeekday (nextWeekday Saturday)) = Tuesday

This declaration does two things: it makes an assertion (that the second weekday
after `Saturday` is `Tuesday`) and it gives the assertion a name that can be
used to refer to it later.

Having made the assertion, we can also ask Idris to verify it, like this:

>   testNextWeekday = Refl

\color{red}
-- TODO: Edit this

The details are not important for now (we'll come back to them in a bit), but
essentially this can be read as "The assertion we've just made can be proved by
observing that both sides of the equality evaluate to the same thing, after some
simplification."
\color{black}

(For simple proofs like this, you can call
\mintinline[]{elisp}{idris-add-clause} (\mintinline[]{elisp}{M-RET d}) with the
point on the name (`testNextWeekday`) in the type signature and then call
\mintinline[]{elisp}{idris-proof-search} (\mintinline[]{elisp}{M-RET p}) with
the point on the resultant hole to have Idris solve the proof for you.)

\color{red}
-- TODO: verify the "main uses" claim.

Third, we can ask Idris to _generate_, from our definition, a program in some
other, more conventional, programming (C, Javascript and Node are bundled with
Idris) with a high-performance compiler. This facility is very interesting,
since it gives us a way to construct _fully certified_ programs in mainstream
languages. Indeed, this is one of the main uses for which Idris was developed.
We'll come back to this topic in later chapters.
\color{black}


== Booleans

> namespace Booleans

In a similar way, we can define the standard type `B` of booleans, with
members `False` and `True`.

>   ||| Boolean Data Type
>   data B : Type where
>     False : B
>     True  : B

Although we are rolling our own booleans here for the sake of building up
everything from scratch, Idiris does, of course, provide a default
implementation of the booleans in its standard library, together with a
multitude of useful functions and lemmas. (Take a look at `Prelude` in the Idris
library documentation if you're interested.) Whenever possible, we'll name our
own definitions and theorems so that they exactly coincide with the ones in the
standard library.

Functions over booleans can be defined in the same way as above:

>   negb : (b : B) -> B
>   negb True  = False
>   negb False = True

>   andb : (b1 : B) -> (b2 : B) -> B
>   andb True  b2 = b2
>   andb False b2 = False

>   ||| Boolean OR.
>   orb : (b1 : B) -> (b2 : B) -> B
>   orb True  b2 = True
>   orb False b2 = b2

The last two illustrate Idris's syntax for multi-argument function definitions.
The corresponding multi-argument application syntax is illustrated by the
following four "unit tests," which constitute a complete specification -- a
truth table -- for the `orb` function:

>   testOrb1 : (orb True  False) = True
>   testOrb1 = Refl
>   testOrb2 : (orb False False) = False
>   testOrb2 = Refl
>   testOrb3 : (orb False True)  = True
>   testOrb3 = Refl
>   testOrb4 : (orb True  True)  = True
>   testOrb4 = Refl

\color{red}
-- TODO: Edit this

We can also introduce some familiar syntax for the boolean operations we have
just defined. The `syntax` command defines new notation for an existing
definition, and `infixl` specifies left-associative fixity.
\color{black}

>   infixl 4 &&, ||

>   (&&) : B -> B -> B
>   (&&) = andb

>   ||| Boolean OR; infix alias for [`orb`](#Basics.Booleans.orb).
>   (||) : B -> B -> B
>   (||) = orb

>   testOrb5 : False || False || True = True
>   testOrb5 = Refl


=== Exercises: 1 star (nandb)

Remove `postulate` and complete the following function; then make sure that the
assertions belof can each be verified by Idris. (Remove `postulate` and fill in
each proof, following the model of the `orb` tests above.) The function should
return `True` if either or both of its inputs `False`.

>   postulate
>   nandb : (b1 : B) -> (b2 : B) -> B
>   -- FILL IN HERE

>   postulate
>   testNandb1 : (nandb True  False) = True
>   -- FILL IN HERE

>   postulate
>   testNandb2 : (nandb False False) = True
>   -- FILL IN HERE

>   postulate
>   testNandb3 : (nandb False True)  = True
>   -- FILL IN HERE

>   postulate
>   testNandb4 : (nandb True  True)  = False
>   -- FILL IN HERE


== Function Types

Every expression in Idris has a type, describing what sort of thing it computes.
The `:type` (or `:t`) REPL command asks Idris to print the type of an
expression.

For example, the type of `negb True` is `B`.

```idris
λΠ> :type True
-- True : B
λΠ> :t negb True : B
-- negb True : B
```

\color{red}
-- TODO: Confirm the "function types" wording.

Functions like `negb` itself are also data values, just like `True` and `False`.
Their types are called _function types_, and they are written with arrows.
\color{black}

```idris
λΠ> :t negb
-- negb : B -> B
```

The type of `negb`, written `B -> B` and pronounced "`B` arrow `B`," can be read,
"Given an input of type `B`, this function produces an output of type `B`."
Similarly, the type of `andb`, written `B -> B -> B`, can be read, "Given
two inputs, both of type `B`, this function produces an output of type
`B`."


== Modules

\color{red}
-- TODO: Flesh this out and discuss namespaces

Idris provides a _module system_, to aid in organizing large developments.
\color{black}

> -- FIXME: Figure out how to redefine `Nat` locally here.
> -- namespace Playground1
> --   %hide Prelude.Nat.Nat


== Numbers

> namespace Numbers

The types we have defined so far are examples of "enumerated types": their
definitions explicitly enumerate a finit set of elements. A More interesting way
of defining a type is to give a collection of _inductive rules_ describing its
elements. For example, we can define the natural numbers as follows:

> -- FIXME:
> --   data Nat : Type where
> --     Z : Nat
> --     S : Nat -> Nat

The clauses of this definition can be read:
- `Z` is a natural number.
- `S` is a "constructor" that takes a natural number and yields another one --
  that is, if `n` is a natural number, then `S n` is too.

Let's look at this in a little more detail.

Every inductively defined set (`Day`, `Nat`, `B`, etc.) is actually a set of
_expressions_. The definition of `Nat` says how expressions in the set `Nat` can
be constructed:

- the expression `Z` belongs to the set `Nat`;
- if `n` is an expression belonging to the set `Nat`, then `S n` is also an
  expression belonging to the set `Nat`; and
- expression formed in these two ways are the only ones belonging to the set
  `Nat`.

The same rules apply for our definitions of `Day` and `B`. The annotations we
used for their constructors are analogous to the one for the `Z` constructor,
indicating that they don't take any arguments.

These three conditions are the precise force of inductive declarations. They
imply that the expression `Z`, the expression `S Z`, the expression `S (S Z)`,
the expression `S (S (S Z))` and so on all belong to the set `Nat`, while other
expressions like `True`, `andb True False`, and `S (S False)` do not.

We can write simple functions that pattern match on natural numbers just as we
did above -- for example, the predecessor function:

> -- FIXME:
> --   pred : (n : Nat) -> Nat
> --   pred Z      = Z
> --   pred (S n') = n'

The second branch can be read: "if `n` has the form `S n'` for some `n'`, then
return `n'`."

>   minusTwo : (n : Nat) -> Nat
>   minusTwo Z          = Z
>   minusTwo (S Z)      = Z
>   minusTwo (S (S n')) = n'

Because natural numbers are such a pervasive form of data, Idris provides a tiny
bit of built-in magic for parsing and printing them: ordinary arabic numerals
can be used as an alternative to the "unary" notation defined by the
constructors `S` and `Z`. Idris prints numbers in arabic form by default:

```idris
λΠ> S (S (S (S Z)))
-- 4 : Nat
λΠ> minusTwo 4
-- 2 : Nat
```

The constructor `S` has the type `Nat -> Nat`, just like the functions
`minusTwo` and `pred`:

```idris
λΠ> :t S
λΠ> :t pred
λΠ> :t minusTwo
```

These are all things that can be applied to a number to yield a number. However,
there is a fundamental difference between the first one and the other two:
functions like `pred` and `minusTwo` come with _computation rules_ -- e.g., the
definition of `pred` says that `pred 2` can be simplified to `1` -- while the
definition of `S` has no such behavior attached. Althrough it is like a function
in the sense that it can be applied to an argument, it does not _do_ anything at
all!

For most function definitions over numbers, just pattern matching is not enough:
we also need recursion. For example, to check that a number `n` is even, we may
need to recursively check whether `n-2` is even.

>   ||| Determine whether a number is even.
>   ||| @n a number
>   evenb : (n : Nat) -> B
>   evenb Z          = True
>   evenb (S Z)      = False
>   evenb (S (S n')) = evenb n'

We can define `oddb` by a similar recursive declaration, but here is a simpler
definition that is a bit easier to work with:

>   ||| Determine whether a number is odd.
>   ||| @n a number
>   oddb : (n : Nat) -> B
>   oddb n = negb (evenb n)

>   testOddb1 : oddb 1 = True
>   testOddb1 = Refl
>   testOddb2 : oddb 4 = False
>   testOddb2 = Refl

Naturally we can also define multi-argument functions by recursion.

> -- FIXME: Figure out how to redefine `plus`, `mult` and `minus` locally here.
> -- namespace Playground2
> --   %hide Prelude.Nat.Nat

> --   plus : (n : Nat) -> (m : Nat) -> Nat
> --   plus Z      m = m
> --   plus (S n') m = S (plus n' m)

Adding three to two now gives us five, as we'd expect.

```idris
λΠ> plus 3 2
```

The simplification that Idris performs to reach this conclusion can be
visualized as follows:

`plus (S (S (S Z))) (S (S Z))`

$\hookrightarrow$ `S (plus (S (S Z)) (S (S Z)))`
                    by the second clause of `plus`

$\hookrightarrow$ `S (S (plus (S Z) (S (S Z))))`
                    by the second clause of `plus`

$\hookrightarrow$ `S (S (S (plus Z (S (S Z)))))`
                    by the second clause of `plus`

$\hookrightarrow$ `S (S (S (S (S Z))))`
                    by the first clause of `plus`

As a notational convenience, if two or more arguments have the same type, they
can be written together. In the following definition, `(n, m : Nat)` means just
the same as if we had written `(n : Nat) -> (m : Nat)`.

> --   mult : (n, m : Nat) -> Nat
> --   mult Z      = Z
> --   mult (S n') = plus m (mult n' m)

>   testMult1 : (mult 3 3) = 9
>   testMult1 = Refl

You can match two expression at once:

> --   minus (n, m : Nat) -> Nat
> --   minus Z      _      = Z
> --   minus n      Z      = n
> --   minus (S n') (S m') = minus n' m'

\color{red}
-- TODO: Verify this.

The `_` in the first line is a _wilcard pattern_. Writing `_` in a pattern is
the same as writing some variable that doesn't get used on the right-hand side.
This avoids the need to invent a bogus variable name.
\color{black}


>   exp : (base, power : Nat) -> Nat
>   exp base Z     = S Z
>   exp base (S p) = mult base (exp base p)


=== Exercise: 1 star (factorial)

Recall the standard mathematical factorial function:

\[
    factorial(n)=
\begin{cases}
    1,                      & \text{if } n = 0 \\
    n \times factorial(n-1),& \text{otherwise}
\end{cases}
\]

Translate this into Idris.

>   postulate
>   factorial : (n : Nat) -> Nat
>   -- FILL IN HERE

>   postulate
>   testFactorial1 : factorial 3 = 6
>   -- FILL IN HERE

>   postulate
>   testFactorial2 : factorial 5 = mult 10 12
>   -- FILL IN HERE

\color{red}
-- FIXME: This breaks things...
-- We can make numerical expressions a little easier to read and write by
-- introducing _notations_ for addition, multiplication, and subtraction.

> -- syntax [x] "+" [y] = plus  x y
> -- syntax [x] "-" [y] = minus x y
> -- syntax [x] "*" [y] = mult  x y

\color{black}

```idris
λΠ> :t (0 + 1) + 1
```

(The details are not important, but interested readers can refer to the optional
"More on Syntax" section at the end of this chapter.)

Note that these do not change the definitions we've already made: they are
simply instructions to the Idris parser to accept `x + y` in place of `plus x y`
and, conversely, to the Idris pretty-printer to display `plus x y` as `x + y`.

The `beq_nat` function tests `Nat`ural numbers for `eq`uality, yielding a
`b`oolean.

>   ||| Test natural numbers for equality.
>   beq_nat : (n, m : Nat) -> B
>   beq_nat Z      Z      = True
>   beq_nat Z      (S m') = False
>   beq_nat (S n') Z      = False
>   beq_nat (S n') (S m') = beq_nat n' m'

The `leb` function tests whether its first argument is less than or equal to its
second argument, yielding a boolean.

>   ||| Test whether a number is less than or equal to another.
>   leb : (n, m : Nat) -> B
>   leb Z      m      = True
>   leb (S n') Z      = False
>   leb (S n') (S m') = leb n' m'

>   testLeb1 : leb 2 2 = True
>   testLeb1 = Refl
>   testLeb2 : leb 2 4 = True
>   testLeb2 = Refl
>   testLeb3 : leb 4 2 = False
>   testLeb3 = Refl


=== Exercise: 1 star (blt_nat)

The `blt_nat` function tests `Nat`ural numbers for `l`ess-`t`han, yielding a
`b`oolean. Instead of making up a new recursive function for this one, define it
in terms of a previously defined function.

>   postulate
>   blt_nat : (n, m : Nat) -> B
>   -- FILL IN HERE

>   postulate
>   test_blt_nat_1 : blt_nat 2 2 = False
>   -- FILL IN HERE
>   postulate
>   test_blt_nat_2 : blt_nat 2 4 = True
>   -- FILL IN HERE
>   postulate
>   test_blt_nat_3 : blt_nat 4 2 = False
>   -- FILL IN HERE


== Proof by Simplification

Now that we've defined a few datatypes and functions, let's turn to stating and
proving properties of their behavior. Actually, we've already started doing
this: each of the functions beginning with `test` in the previous sections makes
a precise claim about the behavior of some function on some particular inputs.
The proofs of these claims were always the same: use `Refl` to check that both
sides contain identical values.

The same sort of "proof by simplification" can be used to prove more interesting
properties as well. For example, the fact that `0` is a "neutral element" for
`+` on the left can be proved just by observing that `0 + n` reduces to `n` no
matter what `n` is, a fact that can be read directly off the definition of
`plus`.

> plus_Z_n : (n : Nat) -> 0 + n = n
> plus_Z_n n = Refl

It will be useful later to know that [reflexivity] does some simplification --
for example, it tries "unfolding" defined terms, replacing them with their
right-hand sides. The reason for this is that, if reflexivity succeeds, the
whole goal is finished and we don't need to look at whatever expanded
expressions `Refl` has created by all this simplification and unfolding.

Other similar theorems can be proved with the same pattern.

> plus_1_l : (n : Nat) -> 1 + n = S n
> plus_1_l n = Refl

> mult_0_l : (n : Nat) -> 0 * n = 0
> mult_0_l n = Refl

The `_l` suffix in the names of these theorems is pronounces "on the left."

Although simplification is powerful enough to prove some fairly general facts,
there are many statements that cannot be handled by simplification alone. For
instance, we cannot use it to prove that `0` is also a neutral element for `+`
_on the right_.


```idris
plus_n_Z : (n : Nat) -> n = n + 0
plus_n_Z n = Refl
```

```idris
plus_n_Z : (n : Nat) -> n = n + 0
plus_n_Z n = Refl
```
```
When checking right hand side of plus_n_Z with expected type
             n = n + 0

     Type mismatch between
             plus n 0 = plus n 0 (Type of Refl)
     and
             n = plus n 0 (Expected type)

     Specifically:
             Type mismatch between
                     plus n 0
             and
                     n
```

(Can you explain why this happens?)

The next chapter will introduce _induction_, a powerful technique that can be
used for proving this goal. For the moment, though, let's look at a few more
simple tactics.

> plus_id_example : (n, m : Nat) -> (n = m)
>                 -> n + n = m + m

Instead of making a universal claim about all numbers `n` and `m`, it talks
about a more specialized property that only holds when `n = m`. The arrow symbol
is pronounced "implies."

As before, we need to be able to reason by assuming the existence of some
numbers `n` and `m`. We also need to assume the hypothesis `n = m`.

-- FIXME
The `intros` tactic will serve to move all three of these from the goal into
assumptions in the current context.

Since `n` and `m` are arbitrary numbers, we can't just use simplification to
prove this theorem. Instead, we prove it by observing that, if we are assuming
`n = m`, then we can replace `n` with `m` in the goal statement and obtain an
equality with the same expression on both sides. The tactic that tells Idris to
perform this replacement is called `rewrite`.

> plus_id_example n m prf = rewrite prf in Refl

The first two variables on the left side move the universally quantified
variables `n` and `m` into the context. The third moves the hypothesis `n = m`
into the context and gives it the name `prf`. The right side tells Idris to
rewrite the current goal (`n + n = m + m`) by replacing the left side of the
equality hypothesis `prf` with the right side.


=== Exercise: 1 star (plus_id_exercise)

Remove "`postulate`" and fill in the proof.

> postulate
> plus_id_exercise : (n, m, o : Nat) -> (n = m) -> (m = o)
>                  -> n + m = m + o

The `postulate` command tells Idris that we want to skip trying to prove this
theorem and just accept it as a given. This can be useful for developing longer
proofs, since we can state subsidiary lemmas that we believe will be useful for
making some larger argument, use `postulate` to accept them on faith for the
moment, and continue working on the main argument until we are sure it makes
sense; then we can go back and fill in the proofs we skipped. Be careful,
though: every time you say `postulate` you are leaving a door open for total
nonsense to enter Idris's nice, rigorous, formally checked world!

We can also use the `rewrite` tactic with a previously proved theorem instead of
a hypothesis from the context. If the statement of the previously proved theorem
involves quantified variables, as in the example below, Idris tries to
instantiate them by matching with the current goal.

> mult_0_plus : (n, m : Nat) -> (0 + n) * m = n * (0 + m)
> mult_0_plus n m = Refl

Unlike in Coq, we don't need to perform such a rewrite for `mult_0_plus` in
Idris and can just use `Refl` instead.


=== Exercise: 2 starts (mult_S_1)

> postulate
> mult_S_1 : (n, m : Nat) -> (m = S n)
>          -> m * (1 + n) = m * m


== Proof by Case Analysis

Of course, not everything can be proved by simple calculation and rewriting: In
general, unknown, hypothetical values (arbitrary numbers, booleans, lists, etc.)
can block simplification. For example, if we try to prove the following fact
using the `Refl` tactic as above, we get stuck.

```idris
plus_1_neq_0_firsttry : (n : Nat) -> beq_nat (n + 1) 0 = False
plus_1_neq_0_firsttry n = Refl -- does nothing!
```

The reason for this is that the definitions of both `beq_nat` and `+` begin by
performing a `match` on their first argument. But here, the first argument to
`+` is the unknown number `n` and the argument to `beq_nat` is the compound
expression `n + 1`; neither can be simplified.

To make progress, we need to consider the possible forms of `n` separately. If
`n` is `Z`, then we can calculate the final result of `beq_nat (n + 1) 0` and
check that it is, indeed, `False`. And if `n = S n'` for some `n'`, then,
although we don't know exactly what number `n + 1` yields, we can calculate
that, at least, it will begin with one `S`, and this is enough to calculate
that, again, `beq_nat (n + 1) 0` will yield `False`.

To tell Idris to consider, separately, the cases where `n = Z` and
where `n = S n'`, simply case split on `n`.

\color{red}
-- TODO: mention case splitting interactively in Emacs, Atom, etc.
\color{black}

> plus_1_neq_0 : (n : Nat) -> beq_nat (n + 1) 0 = False
> plus_1_neq_0 Z      = Refl
> plus_1_neq_0 (S n') = Refl

Case splitting on `n` generates _two_ holes, which we must then prove,
separately, in order to get Idris to accept the theorem.

In this example, each of the holes is easily filled by a single use of `Refl`,
which itself performs some simplification -- e.g., the first one simplifies
`beq_nat (S n' + 1) 0` to `False` by first rewriting `(S n' + 1)` to `S (n' +
1)`, then unfolding `beq_nat`, simplifying its pattern matching.

There are no hard and fast rules for how proofs should be formatted in Idris.
However, if the places where multiple holes are generated are lifted to lemmas,
then the proof will be readable almost no matter what choices are made about
other aspects of layout.

This is also a good place to mention one other piece of somewhat obvious advice
about line lengths. Beginning Idris users sometimes tend to the extremes, either
writing each tactic on its own line or writing entire proofs on one line. Good
style lies somewhere in the middle. One reasonable convention is to limit
yourself to 80-character lines.

The case splitting strategy can be used with any inductively defined datatype.
For example, we use it next to prove that boolean negation is involutive --
i.e., that negation is its own inverse.

> ||| A proof that boolean negation is involutive.
> negb_involutive : (b : B) -> negb (negb b) = b
> negb_involutive True  = Refl
> negb_involutive False = Refl

Note that the case splitting here doesn't introduce any variables because none
of the subcases of the patterns need to bind any, so there is no need to specify
any names.

It is sometimes useful to case split on more than one parameter, generating yet
more proof obligations. For example:

> andb_commutative : (b, c : B) -> andb b c = andb c b
> andb_commutative True  True  = Refl
> andb_commutative True  False = Refl
> andb_commutative False True  = Refl
> andb_commutative False False = Refl

In more complex proofs, it is often better to lift subgoals to lemmas:


> andb_commutative'_rhs_1 : (c : B) -> c = andb c True
> andb_commutative'_rhs_1 True  = Refl
> andb_commutative'_rhs_1 False = Refl

> andb_commutative'_rhs_2 : (c : B) -> False = andb c False
> andb_commutative'_rhs_2 True  = Refl
> andb_commutative'_rhs_2 False = Refl

> andb_commutative' : (b, c : B) -> andb b c = andb c b
> andb_commutative' True  = andb_commutative'_rhs_1
> andb_commutative' False = andb_commutative'_rhs_2


=== Exercise: 2 stars (andb_true_elim2)

Prove the following claim, lift cases (and subcases) to lemmas when case split.

> postulate
> andb_true_elim_2 : (b, c : B) -> (andb b c = True) -> c = True


=== Exercise: 1 star (zero_nbeq_plus

> postulate
> zero_nbeq_plus_1 : (n : Nat) -> beq_nat 0 (n + 1) = False


\color{red}
-- TODO: discuss associativity
\color{black}

== Structural Recursion (Optional)

Here is a copy of the definition of addition:

```idris
plus' : Nat -> Nat -> Nat
plus' Z        right = right
plus' (S left) right = S (plus' left right)
```

When Idris checks this definition, it notes that `plus'` is "decreasing on 1st
argument." What this means is that we are performing a _structural recursion_
over the argument `left` -- i.e., that we make recursive calls only on strictly
smaller values of `left`. This implies that all calls to `plus'` will eventually
terminate. Idris demands that some argument of _every_ recursive definition is
"decreasing."

This requirement is a fundamental feature of Idris's design: In particular, it
guarantees that every function that can be defined in Idris will terminate on
all inputs. However, because Idris's "decreasing analysis" is not very
sophisticated, it is sometimes necessary to write functions in slightly
unnatural ways.

\color{red}
-- TODO: verify the previous claims
\color{black}


== More Exercises

=== Exercise: 2 stars (boolean_functions)

Use the tactics you have learned so far to prove the following theorem about
boolean functions.

> postulate
> identity_fn_applied_twice : (f : B -> B)
>                           -> ((x : B) -> f x = x)
>                           -> (b : B) -> f (f b) = b

Now state and prove a theorem `negation_fn_applied_twice` similar to the
previous one but where the second hypothesis says that the function `f` has the
property that `f x = negb x`.

> postulate
> andb_eq_orb : (b, c : B)
>             -> (andb b c = orb b c)
>             -> b = c


=== Exercise: 3 stars (binary)

Consider a different, more efficient representation of natural numbers using a
binary rather than unary system. That is, instead of saying that each natural
number is either zero or the successor of a natural number, we can say that each
binary number is either

- zero,
- twice a binary number, or
- one more than twice a binary number.

(a) First, write an inductive definition of the type `Bin` corresponding to this
    description of binary numbers.

(Hint: Recall that the definition of `Nat` from class,

```idris
data Nat : Type where
  Z : Nat
  S : Nat -> Nat
```

says nothing about what `Z` and `S` "mean." It just says "`Z` is in the set
called `Nat`, and if `n` is in the set then so is `S n`." The interpretation of
`Z` as zero and `S` as successor/plus one comes from the way that we _use_ `Nat`
values, by writing functions to do things with them, proving things about them,
and so on. Your definition of `Bin` should be correspondingly simple; it is the
functions you will write next that will give it mathematical meaning.)

(b) Next, write an increment function `incr` for binary numbers, and a function
    `bin_to_nat` to convert binary numbers to unary numbers.

(c) Write five unit tests `test_bin_incr_1`, `test_bin_incr_2`, etc. for your
    increment and binary-to-unary functions. Notice that incrementing a binary
    number and then converting it to unary should yield the same result as first
    converting it to unary and then incrementing.
