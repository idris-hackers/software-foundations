= Stlc

== Stlc : The Simply Typed Lambda-Calculus

The simply typed lambda-calculus (STLC) is a tiny core
calculus embodying the key concept of _functional abstraction_,
which shows up in pretty much every real-world programming
language in some form (functions, procedures, methods, etc.).

We will follow exactly the same pattern as in the previous chapter
when formalizing this calculus (syntax, small-step semantics,
typing rules) and its main properties (progress and preservation).
The new technical challenges arise from the mechanisms of
_variable binding_ and _substitution_.  It which will take some
work to deal with these.

> module Stlc
> import Smallstep
> import Types
> import Maps

> %access public export
> %default total
> %hide Types.Tm
> %hide Types.Ty
> %hide Types.(->>)
> %hide Types.(->>*)
> %hide Smallstep.(->>)
> %hide Smallstep.(->>*)
> %hide Types.Has_type

=== Overview

The STLC is built on some collection of _base types_:
booleans, numbers, strings, etc.  The exact choice of base types
doesn't matter much -- the construction of the language and its
theoretical properties work out the same no matter what we
choose -- so for the sake of brevity let's take just `Bool` for
the moment.  At the end of the chapter we'll see how to add more
base types, and in later chapters we'll enrich the pure STLC with
other useful constructs like pairs, records, subtyping, and
mutable state.

Starting from boolean constants and conditionals, we add three
things:
    - variables
    - function abstractions
    - application

This gives us the following collection of abstract syntax
constructors (written out first in informal BNF notation -- we'll
formalize it below).

```
       t ::= x                       variable
           | \x:T1.t2                abstraction
           | t1 t2                   application
           | true                    constant true
           | false                   constant false
           | if t1 then t2 else t3   conditional
```

The `\` symbol in a function abstraction `\x:T1.t2` is generally
written as a Greek letter "lambda" (hence the name of the
calculus).  The variable `x` is called the _parameter_ to the
function; the term `t2` is its _body_.  The annotation `:T1`
specifies the type of arguments that the function can be applied
to.

Some examples:

- `\x:Bool. x`

  The identity function for booleans.

- `(\x:Bool. x) true`

  The identity function for booleans, applied to the boolean `true`.

- `\x:Bool. if x then false else true`

  The boolean "not" function.

- `\x:Bool. true`

  The constant function that takes every (boolean) argument to
  `true`.

- `\x:Bool. \y:Bool. x`

  A two-argument function that takes two booleans and returns
  the first one.  (As in Coq, a two-argument function is really
  a one-argument function whose body is also a one-argument
  function.)

- `(\x:Bool. \y:Bool. x) false true`

  A two-argument function that takes two booleans and returns
  the first one, applied to the booleans `false` and `true`.

  As in Coq, application associates to the left -- i.e., this
  expression is parsed as `((\x:Bool. \y:Bool. x) false) true`.

- `\f:Bool->Bool. f (f true)`

  A higher-order function that takes a _function_ `f` (from
  booleans to booleans) as an argument, applies `f` to `true`,
  and applies `f` again to the result.

- `(\f:Bool->Bool. f (f true)) (\x:Bool. false)`

  The same higher-order function, applied to the constantly
  `false` function.

As the last several examples show, the STLC is a language of
_higher-order_ functions: we can write down functions that take
other functions as arguments and/or return other functions as
results.

The STLC doesn't provide any primitive syntax for defining _named_
functions -- all functions are "anonymous."  We'll see in chapter
`MoreStlc` that it is easy to add named functions to what we've
got -- indeed, the fundamental naming and binding mechanisms are
exactly the same.

The _types_ of the STLC include `Bool`, which classifies the
boolean constants `true` and `false` as well as more complex
computations that yield booleans, plus _arrow types_ that classify
functions.

```
      T ::= Bool
          | T1 -> T2
```

For example:

  - `\x:Bool. false` has type `Bool->Bool`

  - `\x:Bool. x` has type `Bool->Bool`

  - `(\x:Bool. x) true` has type `Bool`

  - `\x:Bool. \y:Bool. x` has type `Bool->Bool->Bool`
                          (i.e., `Bool -> (Bool->Bool)`)

  - `(\x:Bool. \y:Bool. x) false` has type `Bool->Bool`

  - `(\x:Bool. \y:Bool. x) false true` has type `Bool` *)


=== Syntax

We next formalize the syntax of the STLC.

==== Types

> data Ty : Type where
>   TBool  : Ty
>   TArrow : Ty -> Ty -> Ty

> infixr 0 :=>
> (:=>) : Ty -> Ty -> Ty
> (:=>) = TArrow


==== Terms

> infixr 7 #

> data Tm : Type where
>   Tvar    : String -> Tm
>   (#)     : Tm -> Tm -> Tm
>   Tabs    : String -> Ty -> Tm -> Tm
>   Ttrue   : Tm
>   Tfalse  : Tm
>   Tif     : Tm -> Tm -> Tm -> Tm

> syntax "(" "\\" [p] ":" [q] "." [r] ")" = Tabs "p" q r

> syntax "lif" [c] "then" [p] "else" [n] = Tif c p n

> syntax "&" [p] = Tvar "p"

Note that an abstraction `\x:T.t` (formally, `tabs x T t`) is
always annotated with the type `T` of its :parameter, in contrast
to Idris (and other functional languages like ML, Haskell, etc.),
which use type inference to fill in missing annotations.  We're
not considering type inference here.

Some examples...

`idB = \x:Bool. x`

> idB : Tm
> idB = (\x: TBool . &x)

`idBB = \x:Bool->Bool. x`

> idBB : Tm
> idBB = (\x: (TBool :=> TBool) . &x)

`idBBBB = \x:(Bool->Bool) -> (Bool->Bool). x`

> idBBBB : Tm
> idBBBB = (\x: ((TBool :=> TBool) :=> (TBool :=> TBool)). &x)

`k = \x:Bool. \y:Bool. x`

> k : Tm
> k = (\x : TBool . (\y : TBool . &x))

`notB = \x:Bool. if x then false else true`

> notB : Tm
> notB = (\x : TBool . (lif &x then Tfalse else Ttrue))

=== Operational Semantics

To define the small-step semantics of STLC terms, we begin,
as always, by defining the set of values.  Next, we define the
critical notions of _free variables_ and _substitution_, which are
used in the reduction rule for application expressions.  And
finally we give the small-step relation itself.

==== Values

To define the values of the STLC, we have a few cases to consider.

First, for the boolean part of the language, the situation is
clear: `true` and `false` are the only values.  An `if`
expression is never a value.

Second, an application is clearly not a value: It represents a
function being invoked on some argument, which clearly still has
work left to do.

Third, for abstractions, we have a choice:

  - We can say that `\x:T. t1` is a value only when `t1` is a
    value -- i.e., only if the function's body has been
    reduced (as much as it can be without knowing what argument it
    is going to be applied to).

  - Or we can say that `\x:T. t1` is always a value, no matter
    whether `t1` is one or not -- in other words, we can say that
    reduction stops at abstractions.

Our usual way of evaluating expressions in Idris makes the first
choice -- for example,

    Compute (fun x:bool => 3 + 4)

    yields `fun x:bool => 7`.

Most real-world functional programming languages make the second
choice -- reduction of a function's body only begins when the
function is actually applied to an argument.  We also make the
second choice here.

> data Value : Tm -> Type where
>   V_abs : {x: String} -> {T: Ty} -> {t: Tm} -> Value (Tabs x T t)
>   V_true : Value Ttrue
>   V_false : Value Tfalse

Finally, we must consider what constitutes a _complete_ program.

Intuitively, a "complete program" must not refer to any undefined
variables.  We'll see shortly how to define the _free_ variables
in a STLC term.  A complete program is _closed_ -- that is, it
contains no free variables.

(Conversely, a term with free variables is often called an _open
term_.)

Having made the choice not to reduce under abstractions, we don't
need to worry about whether variables are values, since we'll
always be reducing programs "from the outside in," and that means
the `step` relation will always be working with closed terms.

==== Substitution

Now we come to the heart of the STLC: the operation of
substituting one term for a variable in another term.  This
operation is used below to define the operational semantics of
function application, where we will need to substitute the
argument term for the function parameter in the function's body.
For example, we reduce

    (\x:Bool. if x then true else x) false

to

    if false then true else false

by substituting `false` for the parameter `x` in the body of the
function.

In general, we need to be able to substitute some given term `s`
for occurrences of some variable `x` in another term `t`.  In
informal discussions, this is usually written ` [x:=s]t ` and
pronounced "substitute `x` with `s` in `t`."

Here are some examples:

  - `[x:=true] (if x then x else false)`
       yields `if true then true else false`

  - `[x:=true] x` yields `true`

  - `[x:=true] (if x then x else y)` yields `if true then true else y`

  - `[x:=true] y` yields `y`

  - `[x:=true] false` yields `false` (vacuous substitution)

  - `[x:=true] (\y:Bool. if y then x else false)`
       yields `\y:Bool. if y then true else false`

  - `[x:=true] (\y:Bool. x)` yields `\y:Bool. true`

  - `[x:=true] (\y:Bool. y)` yields `\y:Bool. y`

  - `[x:=true] (\x:Bool. x)` yields `\x:Bool. x`

The last example is very important: substituting `x` with `true` in
`\x:Bool. x` does _not_ yield `\x:Bool. true`!  The reason for
this is that the `x` in the body of `\x:Bool. x` is _bound_ by the
abstraction: it is a new, local name that just happens to be
spelled the same as some global name `x`.

Here is the definition, informally...


    [x:=s]x               = s
    [x:=s]y               = y                      if x <> y
    [x:=s](\x:T11. t12)   = \x:T11. t12
    [x:=s](\y:T11. t12)   = \y:T11. [x:=s]t12      if x <> y
    [x:=s](t1 t2)         = ([x:=s]t1) ([x:=s]t2)
    [x:=s]true            = true
    [x:=s]false           = false
    [x:=s](if t1 then t2 else t3) =
                   if [x:=s]t1 then [x:=s]t2 else [x:=s]t3

... and formally:

> subst : String -> Tm -> Tm -> Tm
> subst x s (Tvar x') =
>   case decEq x x' of
>     Yes _ => s
>     No  _ => (Tvar x')
> subst x s (Tabs x' ty t1) =
>       Tabs x' ty (case decEq x x' of
>                     Yes p => t1
>                     No  p => subst x s t1)
> subst x s (t1 # t2) = subst x s t1 # subst x s t2
> subst x s Ttrue = Ttrue
> subst x s Tfalse = Tfalse
> subst x s (Tif t1 t2 t3) = Tif (subst x s t1) (subst x s t2) (subst x s t3)

> syntax "[" [p] ":=" [q] "]" [r] = subst p q r

_Technical note_: Substitution becomes trickier to define if we
consider the case where `s`, the term being substituted for a
variable in some other term, may itself contain free variables.
Since we are only interested here in defining the `step` relation
on _closed_ terms (i.e., terms like `\x:Bool. x` that include
binders for all of the variables they mention), we can avoid this
extra complexity here, but it must be dealt with when formalizing
richer languages.

For example, using the definition of substitution above to
substitute the _open_ term `s = \x:Bool. r`, where `r` is a _free_
reference to some global resource, for the variable `z` in the
term `t = \r:Bool. z`, where `r` is a bound variable, we would get
`\r:Bool. \x:Bool. r`, where the free reference to `r` in `s` has
been "captured" by the binder at the beginning of `t`.

Why would this be bad?  Because it violates the principle that the
names of bound variables do not matter.  For example, if we rename
the bound variable in `t`, e.g., let `t' = \w:Bool. z`, then
`[x:=s]t` is `\w:Bool. \x:Bool. r`, which does not behave the
same as `[x:=s]t = \r:Bool. \x:Bool. r`.  That is, renaming a
bound variable changes how `t` behaves under substitution.

See, for example, `Aydemir 2008` for further discussion
of this issue.

==== Exercise: 3 stars (substi_correct)

The definition that we gave above uses Idris recursive facility
to define substitution as a _function_.  Suppose, instead, we
wanted to define substitution as an inductive _relation_ `substi`.
We've begun the definition by providing the `Inductive` header and
one of the constructors; your job is to fill in the rest of the
constructors and prove that the relation you've defined coincides
with the function given above.

> data Substi : (s:Tm) -> (x:String) -> Tm -> Tm -> Type where
>   S_True  : Substi s x Ttrue Ttrue
>   S_False : Substi s x Tfalse Tfalse
>   S_App   : {l', r':Tm} -> Substi s x l l' -> Substi s x r r' -> Substi s x (l # r) (l' # r')
>   S_If    : {b', p',n':Tm} -> Substi s x b b' -> Substi s x p p'
>               -> Substi s x n n' -> Substi s x (Tif b p n) (Tif b' p' n')
>   S_Var1  : Substi s x (Tvar x) s
>   S_Var2  : Substi s x (Tvar y) (Tvar y)
>   S_Abs1  : Substi s x t t' -> Substi s x (Tabs x' ty t) (Tabs x' ty t')
>   S_Abs2  : Substi s x (Tabs y ty t) (Tabs y ty t)


> substi_correct : (s:Tm) -> (x: String) -> (t : Tm) -> (t' : Tm) ->
>  (([ x := s ] t) = t') <-> Substi s x t t'
> substi_correct s x t t' = ?substi_correct_rhs1

$\square$

== Reduction

The small-step reduction relation for STLC now follows the
same pattern as the ones we have seen before.  Intuitively, to
reduce a function application, we first reduce its left-hand
side (the function) until it becomes an abstraction; then we
reduce its right-hand side (the argument) until it is also a
value; and finally we substitute the argument for the bound
variable in the body of the abstraction.  This last rule, written
informally as

      (\x:T.t12) v2 ->> [x:=v2] t12

is traditionally called "beta-reduction".


\[
  \begin{prooftree}
    \hypo{\idr{value v2}}
    \infer1[\idr{ST_AppAbs}]{\idr{(\x:T.t12) v2 ->> [x:=v2] t12}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{t1 ->> t1'}}
    \infer1[\idr{ST_App1}]{\idr{t1 t2 ->> t1' t2}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{value v1}}
    \hypo{\idr{t2 ->> t2'}}
    \infer2[\idr{ST_App2}]{\idr{v1 t2 ->> v1 t2'}}
  \end{prooftree}
\]

... plus the usual rules for conditionals:

\[
  \begin{prooftree}
    \infer0[\idr{ST_IfTrue}]{\idr{(if true then t1 else t2) ->> t1}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \infer0[\idr{ST_IfFalse}]{\idr{(if false then t1 else t2) ->> t2}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{t1 ->> t1'}}
    \infer1[\idr{ST_If}]{\idr{(if t1 then t2 else t3) ->> (if t1' then t2 else t3)}}
  \end{prooftree}
\]

Formally:

> mutual
>   infixl 6 ->>
>   (->>) : Tm -> Tm -> Type
>   (->>) = Step
>
>   data Step : Tm -> Tm -> Type where
>     ST_AppAbs : {x: String} ->  {ty : Ty} -> {t12 : Tm} -> {v2 : Tm} ->
>       Value v2 ->
>       (Tabs x ty t12) # v2 ->> [ x := v2] t12
>     ST_App1 : {t1, t1', t2: Tm} ->
>       t1 ->> t1' ->
>       t1 # t2 ->> t1' # t2
>     ST_App2 : {v1, t2, t2' : Tm} ->
>       Value v1 ->
>       t2 ->> t2' ->
>       v1 # t2 ->> v1 # t2'
>     ST_IfTrue : {t1, t2: Tm} ->
>       Tif Ttrue t1 t2 ->> t1
>     ST_IfFalse : {t1, t2: Tm} ->
>       Tif Tfalse t1 t2 ->> t2
>     ST_If : {t1, t1', t2, t3: Tm} ->
>       t1 ->> t1' ->
>     Tif t1 t2 t3 ->> Tif t1' t2 t3

> infixl 6 ->>*
> (->>*) : Tm -> Tm -> Type
> (->>*) t t' = Multi Step t t'

=== Examples

Example:

      (\x:Bool->Bool. x) (\x:Bool. x) ->>* \x:Bool. x

    i.e.,

      idBB idB ->>* idB

> step_example1 : Stlc.idBB # Stlc.idB ->>* Stlc.idB
> step_example1 =
>   Multi_step (ST_AppAbs V_abs) Multi_refl

Example:

      (\x:Bool->Bool. x) ((\x:Bool->Bool. x) (\x:Bool. x))
            ->>* \x:Bool. x

    i.e.,

      (idBB (idBB idB)) ->>* idB.

> step_example2 : Stlc.idBB # (Stlc.idBB # Stlc.idB) ->>* Stlc.idB
> step_example2 =
>   Multi_step (ST_App2 V_abs (ST_AppAbs V_abs))
>     (Multi_step (ST_AppAbs V_abs) Multi_refl)

Example:

      (\x:Bool->Bool. x)
         (\x:Bool. if x then false else true)
         true
            ->>* false

    i.e.,

       (idBB notB) ttrue ->>* tfalse.

> step_example3 : (Stlc.idBB # Stlc.notB) # Ttrue ->>* Tfalse
> step_example3 = Multi_step (ST_App1 (ST_AppAbs V_abs))
>                   (Multi_step (ST_AppAbs V_true)
>                     (Multi_step ST_IfTrue Multi_refl))

Example:

    (\x:Bool -> Bool. x)
       ((\x:Bool. if x then false else true) true)
          ->>* false

  i.e.,

    idBB (notB ttrue) ->>* tfalse.

(Note that this term doesn't actually typecheck; even so, we can
ask how it reduces.)

> step_example4 : Stlc.idBB # (Stlc.notB # Ttrue) ->>* Tfalse
> step_example4 = Multi_step (ST_App2 V_abs (ST_AppAbs V_true))
>                   (Multi_step (ST_App2 V_abs ST_IfTrue)
>                     (Multi_step (ST_AppAbs V_false) Multi_refl))

  <!--

(** We can use the `normalize` tactic defined in the `Types` chapter
    to simplify these proofs. *)

Lemma step_example1' :
  (tapp idBB idB) ->>* idB.
Proof. normalize.  Qed.

Lemma step_example2' :
  (tapp idBB (tapp idBB idB)) ->>* idB.
Proof. normalize. Qed.

Lemma step_example3' :
  tapp (tapp idBB notB) ttrue ->>* tfalse.
Proof. normalize.  Qed.

Lemma step_example4' :
  tapp idBB (tapp notB ttrue) ->>* tfalse.
Proof. normalize.  Qed.

-->

==== Exercise: 2 stars (step_example5)

> step_example5 :
>   (Stlc.idBBBB # Stlc.idBB) # Stlc.idB ->>* Stlc.idB
> step_example5 = ?step_example5_rhs

$\square$

=== Typing

Next we consider the typing relation of the STLC.

==== Contexts

_Question_: What is the type of the term "`x y`"

_Answer_: It depends on the types of `x` and `y`!

I.e., in order to assign a type to a term, we need to know
what assumptions we should make about the types of its free
variables.

This leads us to a three-place _typing judgment_, informally
written `Gamma |- t ::T`, where `Gamma` is a
"typing context" -- a mapping from variables to their types.

Following the usual notation for partial maps, we could write `Gamma
& {{x:T}}` for "update the partial function `Gamma` to also map
`x` to `T`."

> Context : Type
> Context = PartialMap Ty

> syntax [context] "&" "{{" [x] "==>" [y] "}}" = update x y context

==== Typing Relation

\[
  \begin{prooftree}
    \hypo{\idr{Gamma x = T}}
    \infer1[\idr{T_Var}]{\idr{Gamma |- x ::T}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{Gamma & {{ x --> T11 }} |- t12 :: T12}}
    \infer1[\idr{T_Abs}]{\idr{Gamma |- \x:T11.t12 ::T11->T12}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{Gamma |- t1 ::T11->T12}}
    \hypo{\idr{Gamma |- t2 ::T11}}
    \infer2[\idr{T_App}]{\idr{Gamma |- t1 t2 ::T12}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \infer0[\idr{T_True}]{\idr{Gamma |- true ::Bool}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \infer0[\idr{T_False}]{\idr{Gamma |- false ::Bool}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{Gamma |- t1 ::Bool}}
    \hypo{\idr{Gamma |- t2 ::T}}
    \hypo{\idr{Gamma |- t3 ::T}}
    \infer3[\idr{T_If}]{\idr{Gamma |- if t1 then t2 else t3 ::T}}
  \end{prooftree}
\]

We can read the three-place relation `Gamma |- t ::T` as:
"under the assumptions in Gamma, the term `t` has the type `T`." *)

> syntax  [context] "|-" [t] "::" [T] "." = Has_type context t T

> data Has_type : Context -> Tm -> Ty -> Type where
>   T_Var : {Gamma: Context} -> {x: String} -> {T: Ty} ->
>      Gamma (MkId x) = Just T ->
>      Gamma |- (Tvar x) :: T .
>   T_Abs : {Gamma: Context} -> {x: String} -> {T11, T12: Ty} -> {t12 : Tm} ->
>      (Gamma & {{ (MkId x) ==> T11 }}) |- t12 :: T12 . ->
>      Gamma |- (Tabs x T11 t12) :: (T11 :=> T12) .
>   T_App : {Gamma: Context} -> {T11, T12: Ty} -> {t1, t2 : Tm} ->
>      Gamma |- t1 :: (T11 :=> T12). ->
>      Gamma |- t2 :: T11 . ->
>      Gamma |- (t1 # t2) :: T12 .
>   T_True : {Gamma: Context} ->
>      Gamma |- Ttrue :: TBool .
>   T_False : {Gamma: Context} ->
>      Gamma |- Tfalse :: TBool .
>   T_If : {Gamma: Context} -> {T : Ty} -> {t1, t2, t3 : Tm} ->
>       Gamma |- t1 :: TBool . ->
>       Gamma |- t2 :: T . ->
>       Gamma |- t3 :: T . ->
>       Gamma |- (Tif t1 t2 t3) :: T .

==== Examples

> typing_example_1 : empty |- (Tabs "x" TBool (Tvar "x")) :: (TBool :=> TBool) .
> typing_example_1 = T_Abs (T_Var Refl)


Another example:

```
       empty |- \x:A. \y:A->A. y (y x)
             ::A -> (A->A) -> A.
```

> typing_example_2 : empty |-
>    (Tabs "x" TBool
>       (Tabs "y" (TBool :=> TBool)
>          (Tvar "y" # Tvar "y" # Tvar "x"))) ::
>    (TBool :=> (TBool :=> TBool) :=> TBool) .
> typing_example_2 =
>   T_Abs (T_Abs (T_App (T_Var Refl) (T_App (T_Var Refl) (T_Var Refl))))


==== Exercise: 2 stars (typing_example_3)

Formally prove the following typing derivation holds:

```
          empty |- \x:Bool->B. \y:Bool->Bool. \z:Bool.
                   y (x z)
             ::T.
```

> typing_example_3 :
>    (T : Ty ** empty |-
>      (Tabs "x" (TBool :=> TBool)
>         (Tabs "y" (TBool :=> TBool)
>            (Tabs "z" TBool
>               (Tvar "y" # (Tvar "x" # Tvar "z"))))) :: T . )
> typing_example_3 = ?typing_example_3_rhs

$\square$

We can also show that terms are _not_ typable.  For example, let's
formally check that there is no typing derivation assigning a type
to the term `\x:Bool. \y:Bool, x y` -- i.e.,

```
    ~ exists T,
        empty |- \x:Bool. \y:Bool, x y ::T.
```

> forallToExistence : {X : Type} -> {P: X -> Type} ->
>   ((a : X) -> Not (P a)) -> Not (a : X ** P a)
> forallToExistence hyp (b ** p2) = hyp b p2

> typing_nonexample_1 :
>   Not (T : Ty **
>     empty |-
>        (Tabs "x" TBool
>            (Tabs "y" TBool
>               (Tvar "x" # Tvar y))) :: T . )
> typing_nonexample_1 = forallToExistence
>   (\ a , (T_Abs (T_Abs (T_App (T_Var Refl)(T_Var Refl)))) impossible)

==== Exercise: 3 stars, optional (typing_nonexample_3)

Another nonexample:

```    ~ (exists S, exists T,
          empty |- \x:S. x x ::T).
```

> typing_nonexample_3 :
>  Not (s : Ty ** t : Ty **
>        empty |-
>          (Tabs "x" s
>             (Tvar "x" # Tvar "x")) :: t . )
> typing_nonexample_3 = ?typing_nonexample_3_rhs

$\square$
