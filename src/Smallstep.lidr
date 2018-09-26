= Library Smallstep

== Smallstep: Small-step Operational Semantics

> module Smallstep
> %access public export
> %default total
> %hide Language.Reflection.P

The evaluators we have seen so far (for `aexp`s, `bexp`s,
commands, ...) have been formulated in a "big-step" style: they
specify how a given expression can be evaluated to its final
value (or a command plus a store to a final store) "all in one big
step."

This style is simple and natural for many purposes -- indeed,
Gilles Kahn, who popularized it, called it _natural semantics_.
But there are some things it does not do well.  In particular, it
does not give us a natural way of talking about _concurrent_
programming languages, where the semantics of a program -- i.e.,
the essence of how it behaves -- is not just which input states
get mapped to which output states, but also includes the
intermediate states that it passes through along the way, since
these states can also be observed by concurrently executing code.

Another shortcoming of the big-step style is more technical, but
critical in many situations.  Suppose we want to define a variant
of Imp where variables could hold _either_ numbers _or_ lists of
numbers.  In the syntax of this extended language, it will be
possible to write strange expressions like `2 + nil`, and our
semantics for arithmetic expressions will then need to say
something about how such expressions behave.  One possibility is
to maintain the convention that every arithmetic expressions
evaluates to some number by choosing some way of viewing a list as
a number -- e.g., by specifying that a list should be interpreted
as `0` when it occurs in a context expecting a number.  But this
is really a bit of a hack.

A much more natural approach is simply to say that the behavior of
an expression like `2+nil` is _undefined_ -- i.e., it doesn't
evaluate to any result at all.  And we can easily do this: we just
have to formulate `aeval` and `beval` as `Inductive` propositions
rather than Fixpoints, so that we can make them partial functions
instead of total ones.

Now, however, we encounter a serious deficiency.  In this
language, a command might fail to map a given starting state to
any ending state for _two quite different reasons_: either because
the execution gets into an infinite loop or because, at some
point, the program tries to do an operation that makes no sense,
such as adding a number to a list, so that none of the evaluation
rules can be applied.

These two outcomes -- nontermination vs. getting stuck in an
erroneous configuration -- should not be confused.  In particular, we
want to _allow_ the first (permitting the possibility of infinite
loops is the price we pay for the convenience of programming with
general looping constructs like `while`) but _prevent_ the
second (which is just wrong), for example by adding some form of
_typechecking_ to the language.  Indeed, this will be a major
topic for the rest of the course.  As a first step, we need a way
of presenting the semantics that allows us to distinguish
nontermination from erroneous "stuck states."

So, for lots of reasons, we'd often like to have a finer-grained
way of defining and reasoning about program behaviors.  This is
the topic of the present chapter.  Our goal is to replace the
"big-step" `eval` relation with a "small-step" relation that
specifies, for a given program, how the "atomic steps" of
computation are performed.

== A Toy Language

To save space in the discussion, let's go back to an
incredibly simple language containing just constants and
addition.  (We use single letters -- `C` and `P` (for Constant and
Plus) -- as constructor names, for brevity.)  At the end of the
chapter, we'll see how to apply the same techniques to the full
Imp language.

> data Tm : Type where
>   C : Nat -> Tm         -- Constant
>   P : Tm -> Tm -> Tm    -- Plus

Here is a standard evaluator for this language, written in
    the big-step style that we've been using up to this point.

> evalF : (t : Tm) -> Nat
> evalF (C n) = n
> evalF (P a1 a2) = evalF a1 + evalF a2

Here is the same evaluator, written in exactly the same
    style, but formulated as an inductively defined relation.  Again,
    we use the notation `t >>> n` for "`t` evaluates to `n`."

\[
  \begin{prooftree}
    \infer0[\idr{E_Const}]{\idr{C n >>> n}}
  \end{prooftree}
  \newline
\]

\[
  \begin{prooftree}
    \hypo{\idr{t1 >>> n1}}
    \hypo{\idr{t1 >>> n2}}
    \infer2[\idr{E_Plus}]{\idr{P t1 t2 >>> n1 + n2}}
  \end{prooftree}
\]

> infixl 6 >>>

> mutual
>   (>>>) : Tm -> Nat -> Type
>   (>>>) = Eval
>
>   data Eval : Tm -> Nat -> Type where
>     E_Const : C n >>> n
>     E_Plus  : t1 >>> n1 -> t2 >>> n2 -> P t1 t2 >>> n1 + n2
>


Now, here is the corresponding _small-step_ evaluation relation.

\[
  \begin{prooftree}
    \infer0[\idr{ST_PlusConstConst'}]{\idr{P (C n1) (C n2) ->> C (n1 + n2)}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{t1 ->> t1'}}
    \infer1[\idr{ST_Plus1'}]{\idr{P t1 t2 ->> P t1' t2}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{t2 ->> t2'}}
    \infer1[\idr{ST_Plus2'}]{\idr{P (C n1) t2 ->> P (C n1) t2'}}
  \end{prooftree}
\]

> mutual
>   infixl 6 ->>
>   (->>) : Tm -> Tm -> Type
>   (->>) = Step'
>
>   data Step' : Tm -> Tm -> Type where
>     ST_PlusConstConst' : P (C n1) (C n2) ->> C (n1 + n2)
>     ST_Plus1' : t1 ->> t1' -> P t1 t2 ->> P t1' t2
>     ST_Plus2' : t2 ->> t2' -> P (C n1) t2 ->> P (C n1) t2'
>

Things to notice:

- We are defining just a single reduction step, in which
  one `P` node is replaced by its value.

- Each step finds the _leftmost_ `P` node that is ready to
  go (both of its operands are constants) and rewrites it in
  place.  The first rule tells how to rewrite this `P` node
  itself; the other two rules tell how to find it.

- A term that is just a constant cannot take a step.

Let's pause and check a couple of examples of reasoning with
    the `step` relation...

If `t1` can take a step to `t1'`, then `P t1 t2` steps
    to `P t1' t2`:

>   test_step_1 :
>      P
>        (P (C 0) (C 3))
>        (P (C 2) (C 4))
>      ->>
>      P
>        (C (0 + 3))
>        (P (C 2) (C 4))
>   test_step_1  = ST_Plus1' ST_PlusConstConst'


==== Exercise: 1 star (test_step_2)
Right-hand sides of sums can take a step only when the
    left-hand side is finished: if `t2` can take a step to `t2'`,
    then `P (C n) t2` steps to `P (C n) t2'`:

>   test_step_2 :
>      P
>        (C 0)
>        (P
>          (C 2)
>          (P (C 0) (C 3)))
>      ->>
>      P
>        (C 0)
>        (P
>          (C 2)
>          (C (0 + 3)))
>   test_step_2 = ?test_step_2_rhs

$\square$

== Relations

We will be working with several different single-step relations,
    so it is helpful to generalize a bit and state a few definitions
    and theorems about relations in general.  (The optional chapter
    `Rel.lidr` develops some of these ideas in a bit more detail; it may
    be useful if the treatment here is too dense.

A _binary relation_ on a set `X` is a family of propositions
parameterized by two elements of `X` -- i.e., a proposition about
pairs of elements of `X`.

> Relation : Type -> Type
> Relation t = t -> t -> Type

Our main examples of such relations in this chapter will be
    the single-step reduction relation, `->>`, and its multi-step
    variant, `->>*` (defined below), but there are many other
    examples -- e.g., the "equals," "less than," "less than or equal
    to," and "is the square of" relations on numbers, and the "prefix
    of" relation on lists and strings.

One simple property of the `->>` relation is that, like the
    big-step evaluation relation for Imp, it is _deterministic_.

_Theorem_: For each `t`, there is at most one `t'` such that `t`
steps to `t'` (`t ->> t'` is provable).  This is the
same as saying that `->>` is deterministic.

_Proof sketch_: We show that if `x` steps to both `y1` and
    `y2`, then `y1` and `y2` are equal, by induction on a derivation
    of `step x y1`.  There are several cases to consider, depending on
    the last rule used in this derivation and the last rule in the
    given derivation of `step x y2`.

- If both are `ST_PlusConstConst'`, the result is immediate.

- The cases when both derivations end with `ST_Plus1` or
  `ST_Plus2` follow by the induction hypothesis.

- It cannot happen that one is `ST_PlusConstConst'` and the other
  is `ST_Plus1` or `ST_Plus2'`, since this would imply that `x`
  has the form `P t1 t2` where both `t1` and `t2` are
  constants (by `ST_PlusConstConst'`) _and_ one of `t1` or `t2`
  has the form `P _`.

- Similarly, it cannot happen that one is `ST_Plus1'` and the
  other is `ST_Plus2'`, since this would imply that `x` has the
  form `P t1 t2` where `t1` has both the form `P t11 t12` and the
  form `C n`.

Formally:


> deterministic : {xt: Type} -> {x: xt} -> {y1: xt} -> {y2: xt} -> (r: Relation xt) -> Type
> deterministic {xt} {x} {y1} {y2} r =  r x y1 -> r x y2 -> y1 = y2


> step_deterministic : deterministic Step'
> step_deterministic ST_PlusConstConst' hyp =
>   case hyp of
>     ST_PlusConstConst' => Refl
>     ST_Plus1' _ impossible
>     ST_Plus2' _ impossible
> step_deterministic (ST_Plus1' l) hyp =
>   case hyp of
>     ST_PlusConstConst' impossible
>     ST_Plus1' l' => rewrite step_deterministic l l' in Refl
>     ST_Plus2' _ impossible
> step_deterministic (ST_Plus2' r) hyp =
>   case hyp of
>     ST_PlusConstConst' impossible
>     ST_Plus1' _ impossible
>     ST_Plus2' r' => rewrite step_deterministic r r' in Refl


=== Values

Next, it will be useful to slightly reformulate the
    definition of single-step reduction by stating it in terms of
    "values."

It is useful to think of the `->>` relation as defining an
    _abstract machine_:

- At any moment, the _state_ of the machine is a term.

- A _step_ of the machine is an atomic unit of computation --
  here, a single "add" operation.

- The _halting states_ of the machine are ones where there is no
  more computation to be done. *)

We can then execute a term `t` as follows:

- Take `t` as the starting state of the machine.

- Repeatedly use the `->>` relation to find a sequence of
  machine states, starting with `t`, where each state steps to
  the next.

- When no more reduction is possible, "read out" the final state
  of the machine as the result of execution.

Intuitively, it is clear that the final states of the
    machine are always terms of the form `C n` for some `n`.
    We call such terms _values_.

> data Value : Tm -> Type where
>   V_const : (n : Nat) -> Value (C n)
>

Having introduced the idea of values, we can use it in the
    definition of the `>>-` relation to write `ST_Plus2` rule in a
    slightly more elegant way:


\[
  \begin{prooftree}
    \infer0[\idr{ST_PlusConstConst}]{\idr{P (C n1) (C n2) >>- C (n1 + n2)}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{t1 >>- t1'}}
    \infer1[\idr{ST_Plus1}]{\idr{P t1 t2 >>- P t1' t2}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
  \hypo{\idr{value v1}}
    \hypo{\idr{t2 >>- t2'}}
    \infer2[\idr{ST_Plus2}]{\idr{P v1 t2 >>- P v1 t2'}}
  \end{prooftree}
\]

Again, the variable names here carry important information:
    by convention, `v1` ranges only over values, while `t1` and `t2`
    range over arbitrary terms.  (Given this convention, the explicit
    `value` hypothesis is arguably redundant.  We'll keep it for now,
    to maintain a close correspondence between the informal and Coq
    versions of the rules, but later on we'll drop it in informal
    rules for brevity.)

Here are the formal rules:

> mutual
>   infixl 6 >>-
>   (>>-) : Tm -> Tm -> Type
>   (>>-) = Step
>
>   data Step : Tm -> Tm -> Type where
>     ST_PlusConstConst : P (C n1) (C n2) >>- C (n1 + n2)
>     ST_Plus1 : t1 >>- t1' -> P t1 t2 >>- P t1' t2
>     ST_Plus2 : Value v1 -> t2 >>- t2' -> P v1 t2 >>- P v1 t2'

==== Exercise: 3 stars, recommended (redo_determinism)

As a sanity check on this change, let's re-verify determinism.

_Proof sketch_: We must show that if `x` steps to both `y1` and
`y2`, then `y1` and `y2` are equal.  Consider the final rules used
in the derivations of `step x y1` and `step x y2`.

- If both are `ST_PlusConstConst`, the result is immediate.

- It cannot happen that one is `ST_PlusConstConst` and the other
  is `ST_Plus1` or `ST_Plus2`, since this would imply that `x` has
  the form `P t1 t2` where both `t1` and `t2` are constants (by
  `ST_PlusConstConst`) _and_ one of `t1` or `t2` has the form `P _`.

- Similarly, it cannot happen that one is `ST_Plus1` and the other
  is `ST_Plus2`, since this would imply that `x` has the form `P
  t1 t2` where `t1` both has the form `P t11 t12` and is a
  value (hence has the form `C n`).

- The cases when both derivations end with `ST_Plus1` or
  `ST_Plus2` follow by the induction hypothesis.

Most of this proof is the same as the one above.  But to get
    maximum benefit from the exercise you should try to write your
    formal version from scratch and just use the earlier one if you
    get stuck.

> step_deterministic' : deterministic Step
> step_deterministic' = ?step_deterministic_rhs
>

$\square$

=== Strong Progress and Normal Forms

The definition of single-step reduction for our toy language
    is fairly simple, but for a larger language it would be easy to
    forget one of the rules and accidentally create a situation where
    some term cannot take a step even though it has not been
    completely reduced to a value.  The following theorem shows that
    we did not, in fact, make such a mistake here.

_Theorem_ (_Strong Progress_): If `t` is a term, then either `t`
    is a value or else there exists a term `t'` such that `t >>- t'`.

_Proof_: By induction on `t`.

- Suppose `t = C n`. Then `t` is a value.

- Suppose `t = P t1 t2`, where (by the IH) `t1` either is a value
  or can step to some `t1'`, and where `t2` is either a value or
  can step to some `t2'`. We must show `P t1 t2` is either a value
  or steps to some `t'`.

  - If `t1` and `t2` are both values, then `t` can take a step, by
    `ST_PlusConstConst`.

  - If `t1` is a value and `t2` can take a step, then so can `t`,
    by `ST_Plus2`.

  - If `t1` can take a step, then so can `t`, by `ST_Plus1`.

Or, formally:

> strong_progress : (t: Tm) -> Either (Value t) (t': Tm ** Step t t')

> strong_progress (C n) = Left (V_const n)
> strong_progress (P (C n) r) = Right $
>    case r of
>       (C n')    =>  (C (n + n') ** ST_PlusConstConst)
>       (P l' r') =>  case strong_progress (P l' r') of
>                           Right (r ** prf1) => (P (C n) r ** ST_Plus2 (V_const n) prf1)
>                           Left (V_const (P l r)) impossible
> strong_progress (P (P l' r') r) = Right $
>     case strong_progress (P l' r') of
>       Right (l ** prf1) => (P l r  ** ST_Plus1 prf1)
>       Left (V_const (P l r)) impossible

This important property is called _strong progress_, because
    every term either is a value or can "make progress" by stepping to
    some other term.  (The qualifier "strong" distinguishes it from a
    more refined version that we'll see in later chapters, called
    just _progress_.)

The idea of "making progress" can be extended to tell us something
    interesting about values: in this language, values are exactly the
    terms that _cannot_ make progress in this sense.

To state this observation formally, let's begin by giving a name
    to terms that cannot make progress.  We'll call them _normal
    forms_.

> normal_form : {X:Type} -> Relation X -> X -> Type
> normal_form r t = Not (t' ** r t t')

Note that this definition specifies what it is to be a normal form
    for an _arbitrary_ relation `R` over an arbitrary set `X`, not
    just for the particular single-step reduction relation over terms
    that we are interested in at the moment.  We'll re-use the same
    terminology for talking about other relations later in the
    course.

We can use this terminology to generalize the observation we made
    in the strong progress theorem: in this language, normal forms and
    values are actually the same thing.

> value_is_nf : (v : Tm) -> Value v -> normal_form Step v
> value_is_nf (C n) prf = notStepCN
>   where notStepCN: (t' : Tm ** Step (C n) t') -> Void
>         notStepCN (t' ** c) impossible
> value_is_nf (P l r) prf = void (notValueP prf)
>   where notValueP: Not (Value (P l r))
>         notValueP (V_const _) impossible

> nf_is_value : (v : Tm) -> normal_form Step v -> Value v
> nf_is_value (C n) prf = V_const n
> nf_is_value (P l r) prf =
>   case strong_progress (P l r) of
>     Left va => va
>     Right pa => void (prf pa)

> iff : (p,q : Type) -> Type
> iff p q = (p -> q, q -> p)

> infixl 6 <->
> (<->) : (p: Type) -> (q:Type) -> Type
> (<->) = iff


> nf_same_as_value : (normal_form Step t) <-> (Value t)
> nf_same_as_value {t} = (nf_is_value t,value_is_nf t)

Why is this interesting?

Because `value` is a syntactic concept -- it is defined by looking
at the form of a term -- while `normal_form` is a semantic one --
it is defined by looking at how the term steps.  It is not obvious
that these concepts should coincide!

Indeed, we could easily have written the definitions so that they
    would _not_ coincide.

==== Exercise: 3 stars, optional (value_not_same_as_normal_form1)

We might, for example, mistakenly define `value` so that it
    includes some terms that are not finished reducing.

(Even if you don't work this exercise and the following ones
    in Idris, make sure you can think of an example of such a term.)


> data Value' : Tm -> Type where
>   V_const' : {n: Nat} -> Value' (C n)
>   V_funny : {t1: Tm} -> {n2: Nat} -> Value' (P t1 (C n2))

> mutual
>   infixl 6 >>>-
>   (>>>-) : Tm -> Tm -> Type
>   (>>>-) = Step''
>
>   data Step'' : Tm -> Tm -> Type where
>     ST_PlusConstConst'' : P (C n1) (C n2) >>>- C (n1 + n2)
>     ST_Plus1'' :
>       t1 >>>- t1' ->
>       P t1 t2 >>>- P t1' t2
>     ST_Plus2'' :
>       Value' v1 ->
>       t2 >>>- t2' ->
>       P v1 t2 >>>- P v1 t2'

> value_not_same_as_normal_form : (v : Tm ** (Value' v, Not (normal_form Step'' v)))
> value_not_same_as_normal_form = ?value_not_same_as_normal_form_rhs

$\square$

==== Exercise: 2 stars, optional (value_not_same_as_normal_form2)

Alternatively, we might mistakenly define `step` so that it
    permits something designated as a value to reduce further.

> mutual
>   infixl 6 ->>>-
>   (->>>-) : Tm -> Tm -> Type
>   (->>>-) = Step'''
>
>   data Step''' : Tm -> Tm -> Type where
>     ST_Funny : C n ->>>- P (C n) (C 0)
>     ST_PlusConstConst''' : P (C n1) (C n2) ->>>- C (n1 + n2)
>     ST_Plus1''' :
>       t1 ->>>- t1' ->
>       P t1 t2 ->>>- P t1' t2
>     ST_Plus2''' :
>       Value' v1 ->
>       t2 ->>>- t2' ->
>       P v1 t2 ->>>- P v1 t2'

> value_not_same_as_normal_form''' : (v : Tm ** (Value v, Not (normal_form Step''' v)))
> value_not_same_as_normal_form''' = ?value_not_same_as_normal_form_rhs'''

$\square$

==== Exercise: 3 stars, optional (value_not_same_as_normal_form3)

Finally, we might define `value` and `step` so that there is some
    term that is not a value but that cannot take a step in the `step`
    relation.  Such terms are said to be _stuck_. In this case this is
    caused by a mistake in the semantics, but we will also see
    situations where, even in a correct language definition, it makes
    sense to allow some terms to be stuck.

> mutual
>   infixl 6 ->>-
>   (->>-) : Tm -> Tm -> Type
>   (->>-) = Step''''
>
>   data Step'''' : Tm -> Tm -> Type where
>     ST_PlusConstConst'''' : P (C n1) (C n2) ->>- C (n1 + n2)
>     ST_Plus1'''' :
>       t1 ->>- t1' ->
>       P t1 t2 ->>- P t1' t2

(Note that `ST_Plus2` is missing.)

> value_not_same_as_normal_form'''' : (t : Tm ** (Not (Value t), normal_form Step'''' t))
> value_not_same_as_normal_form'''' = ?value_not_same_as_normal_form_rhs''''

$\square$


=== Additional Exercises

Here is another very simple language whose terms, instead of being
    just addition expressions and numbers, are just the booleans true
    and false and a conditional expression...

> data TmB : Type where
>   Ttrue : TmB
>   Tfalse : TmB
>   Tif : TmB -> TmB -> TmB -> TmB

> data ValueB : TmB -> Type where
>   V_true : ValueB Ttrue
>   V_false : ValueB Tfalse


> mutual
>   infixl 6 ->-
>   (->-) : TmB -> TmB -> Type
>   (->-) = StepB
>
>   data StepB : TmB -> TmB -> Type where
>     ST_IfTrue : Tif Ttrue t1 t2 ->- t1
>     ST_IfFalse : Tif Tfalse t1 t2 ->- t2
>     ST_If : t1 ->- t1' -> Tif t1 t2 t3 ->- Tif t1' t2 t3


==== Exercise: 1 star (smallstep_bools)

Which of the following propositions are provable?  (This is just a
    thought exercise, but for an extra challenge feel free to prove
    your answers in Idris.)

> bool_step_prop1 : Tfalse ->- Tfalse
> bool_step_prop1 = ?bool_step_prop1_rhs

> bool_step_prop2 :
>     Tif
>       Ttrue
>       (Tif Ttrue Ttrue Ttrue)
>       (Tif Tfalse Tfalse Tfalse)
>  ->-
>     Ttrue
> bool_step_prop2 = ?bool_step_prop2_rhs

> bool_step_prop3 :
>     Tif
>       (Tif Ttrue Ttrue Ttrue)
>       (Tif Ttrue Ttrue Ttrue)
>       Tfalse
>   ->-
>     Tif
>       Ttrue
>       (Tif Ttrue Ttrue Ttrue)
>       Tfalse
> bool_step_prop3 = ?bool_step_prop3_rhs

$\square$


==== Exercise: 3 stars, optional (progress_bool)

Just as we proved a progress theorem for plus expressions, we can
    do so for boolean expressions, as well.

> strong_progressB : {t : TmB} -> (ValueB t, (t': TmB ** t ->- t'))
> strong_progressB = ?strong_progressB_rhs

==== Exercise: 2 stars, optional (step_deterministic)

> step_deterministicB : deterministic StepB
> step_deterministicB = ?step_deterministicB_rhs

==== Exercise: 2 stars (smallstep_bool_shortcut)

Suppose we want to add a "short circuit" to the step relation for
    boolean expressions, so that it can recognize when the `then` and
    `else` branches of a conditional are the same value (either
    `ttrue` or `tfalse`) and reduce the whole conditional to this
    value in a single step, even if the guard has not yet been reduced
    to a value. For example, we would like this proposition to be
    provable:

```idris
     tif
        (tif ttrue ttrue ttrue)
        tfalse
        tfalse
 ->>
     tfalse.
```

Write an extra clause for the step relation that achieves this
    effect and prove `bool_step_prop4`.

> mutual
>   infixl 6 ->->
>   (->->) : TmB -> TmB -> Type
>   (->->) = StepB'
>
>   data StepB' : TmB -> TmB -> Type where
>     ST_IfTrue' : Tif Ttrue t1 t2 ->-> t1
>     ST_IfFalse' : Tif Tfalse t1 t2 ->-> t2
>     ST_If' : t1 ->-> t1' -> Tif t1 t2 t3 ->-> Tif t1' t2 t3

> bool_step_prop4 :
>         Tif
>            (Tif Ttrue Ttrue Ttrue)
>            Tfalse
>            Tfalse
>     ->->
>         Tfalse

> bool_step_prop4_holds : bool_step_prop4
> bool_step_prop4_holds = ?bool_step_prop4_holds_rhs

$\square$


==== Exercise: 3 stars, optional (properties_of_altered_step)
It can be shown that the determinism and strong progress theorems
    for the step relation in the lecture notes also hold for the
    definition of step given above.  After we add the clause
    `ST_ShortCircuit`...

- Is the `step` relation still deterministic?  Write yes or no and
  briefly (1 sentence) explain your answer.

Optional: prove your answer correct in Idris.

- Does a strong progress theorem hold? Write yes or no and
 briefly (1 sentence) explain your answer.

 Optional: prove your answer correct in Idris.

In general, is there any way we could cause strong progress to
fail if we took away one or more constructors from the original
step relation? Write yes or no and briefly (1 sentence) explain
your answer.

$\square$

== Multi-Step Reduction

We've been working so far with the _single-step reduction_
relation `->>`, which formalizes the individual steps of an
abstract machine for executing programs.

We can use the same machine to reduce programs to completion -- to
find out what final result they yield.  This can be formalized as
follows:

- First, we define a _multi-step reduction relation_ `->>*`, which
  relates terms `t` and `t'` if `t` can reach `t'` by any number
  (including zero) of single reduction steps.

- Then we define a "result" of a term `t` as a normal form that
  `t` can reach by multi-step reduction.

Since we'll want to reuse the idea of multi-step reduction many
times, let's take a little extra trouble and define it
generically.

Given a relation `R`, we define a relation `multi R`, called the
multi-step closure of `R`_ as follows.

> mutual
>   infixl 6 ->>*
>   (->>*) : Tm -> Tm -> Type
>   (->>*) t t' = Multi Step t t'
>
>   data Multi: {X: Type} -> (R: Relation X) -> Relation X where
>     Multi_refl  : {X: Type} -> {R: Relation X} -> {x : X} ->  Multi R x x
>     Multi_step  : {X: Type} -> {R: Relation X} -> {x, y, z : X} ->
>                       R x y -> Multi R y z -> Multi R x z

(In the `Rel` chapter of _Logical Foundations_ this relation is called
`clos_refl_trans_1n`.  We give it a shorter name here for the sake
of readability.)

The effect of this definition is that `multi R` relates two
elements `x` and `y` if

- `x = y`, or
- `R x y`, or
- there is some nonempty sequence `z1`, `z2`, ..., `zn` such that

   R x z1
   R z1 z2
   ...
   R zn y.

Thus, if `R` describes a single-step of computation, then `z1`...`zn`
is the sequence of intermediate steps of computation between `x` and
`y`.

We write `->>*` for the `multi step` relation on terms.

The relation `multi R` has several crucial properties.

First, it is obviously _reflexive_ (that is, `forall x, multi R x
x`).  In the case of the `->>*` (i.e., `multi step`) relation, the
intuition is that a term can execute to itself by taking zero
steps of execution.

Second, it contains `R` -- that is, single-step executions are a
particular case of multi-step executions.  (It is this fact that
justifies the word "closure" in the term "multi-step closure of
`R`.")


> multi_R : {X: Type} -> {R: Relation X} -> (x,y: X) -> R x y -> (Multi R) x y
> multi_R x y h = Multi_step h (Multi_refl)

Third, `multi R` is _transitive_.

> multi_trans: {X:Type} -> {R: Relation X} -> {x, y, z : X} ->
>   Multi R x y  -> Multi R y z -> Multi R x z
> multi_trans m1 m2 =
>    case m1 of
>      Multi_refl => m2
>      Multi_step r mx =>
>         let indHyp = multi_trans mx m2
>         in Multi_step r indHyp

In particular, for the `multi step` relation on terms, if
    `t1->>*t2` and `t2->>*t3`, then `t1->>*t3`.

=== Examples

Here's a specific instance of the `multi step` relation:

> test_multistep_1:
>      P
>        (P (C 0) (C 3))
>        (P (C 2) (C 4))
>   ->>*
>      C ((0 + 3) + (2 + 4))
> test_multistep_1 =
>   let z = C ((0 + 3) + (2 + 4))
>   in Multi_step {z=z} (ST_Plus1 ST_PlusConstConst)
>       (Multi_step {z=z} (ST_Plus2 (V_const 3) ST_PlusConstConst)
>         (Multi_step ST_PlusConstConst Multi_refl))


==== Exercise: 1 star, optional (test_multistep_2)

> test_multistep_2: C 3 ->>* C 3
> test_multistep_2 = ?test_multistep_2_rhs

$\square$

==== Exercise: 1 star, optional (test_multistep_3)

> test_multistep_3:
>      P (C 0) (C 3)
>   ->>*
>      P (C 0) (C 3)
> test_multistep_3 = ?test_multistep_3_rhs

$\square$

==== Exercise: 2 stars (test_multistep_4)

> test_multistep_4:
>      P
>        (C 0)
>        (P
>          (C 2)
>          (P (C 0) (C 3)))
>  ->>*
>      P
>        (C 0)
>        (C (2 + (0 + 3)))
> test_multistep_4 = ?test_multistep_4_rhs

$\square$

=== Normal Forms Again

If `t` reduces to `t'` in zero or more steps and `t'` is a
    normal form, we say that "`t'` is a normal form of `t`."

> step_normal_form : (t : Tm) -> Type
> step_normal_form = normal_form Step

> normal_form_of : Tm -> Tm -> Type
> normal_form_of t t' = (t ->>* t', step_normal_form t')

We have already seen that, for our language, single-step reduction is
    deterministic -- i.e., a given term can take a single step in
    at most one way.  It follows from this that, if `t` can reach
    a normal form, then this normal form is unique.  In other words, we
    can actually pronounce `normal_form t t'` as "`t'` is _the_
    normal form of `t`."

==== Exercise: 3 stars, optional (normal_forms_unique)

> normal_forms_unique : deterministic Smallstep.normal_form_of
> normal_forms_unique (l,r) (l2,r2) = ?normal_forms_unique_rhs

$\square$

Indeed, something stronger is true for this language (though not
    for all languages): the reduction of _any_ term `t` will
    eventually reach a normal form -- i.e., `normal_form_of` is a
    _total_ function.  Formally, we say the `step` relation is
    _normalizing_.

> normalizing : {x: Type} -> (r: Relation x) -> Type
> normalizing {x} {r} = (t: x) -> (t' : x ** (Multi r t t', normal_form r t'))

To prove that `step` is normalizing, we need a couple of lemmas.

First, we observe that, if `t` reduces to `t'` in many steps, then
the same sequence of reduction steps within `t` is also possible
when `t` appears as the left-hand child of a `P` node, and
similarly when `t` appears as the right-hand child of a `P`
node whose left-hand child is a value.

> multistep_congr_1 : (t1 ->>* t1') -> ((P t1 t2) ->>* P t1' t2)
> multistep_congr_1 mult =
>   case mult of
>     Multi_refl => Multi_refl
>     Multi_step step mult' =>
>       let indHyp = multistep_congr_1 mult'
>       in Multi_step (ST_Plus1 step) indHyp


==== Exercise: 2 stars (multistep_congr_2)

> multistep_congr_2 : {v:Value t1} -> (t2 ->>* t2') -> ((P t1 t2) ->>* P t1 t2')
> multistep_congr_2 {v=V_const i} mult = ?multistep_congr_2_rhs

$\square$

With these lemmas in hand, the main proof is a straightforward
    induction.

_Theorem_: The `step` function is normalizing -- i.e., for every
    `t` there exists some `t'` such that `t` steps to `t'` and `t'` is
    a normal form.

_Proof sketch_: By induction on terms.  There are two cases to
    consider:

- `t = C n` for some `n`.  Here `t` doesn't take a step, and we
  have `t' = t`.  We can derive the left-hand side by reflexivity
  and the right-hand side by observing (a) that values are normal
  forms (by `nf_same_as_value`) and (b) that `t` is a value (by
  `v_const`).

- `t = P t1 t2` for some `t1` and `t2`.  By the IH, `t1` and `t2`
  have normal forms `t1'` and `t2'`.  Recall that normal forms are
  values (by `nf_same_as_value`); we know that `t1' = C n1` and
  `t2' = C n2`, for some `n1` and `n2`.  We can combine the `->>*`
  derivations for `t1` and `t2` using `multi_congr_1` and
  `multi_congr_2` to prove that `P t1 t2` reduces in many steps to
  `C (n1 + n2)`.

  It is clear that our choice of `t' = C (n1 + n2)` is a value,
  which is in turn a normal form. `` *)

> step_normalizing : normalizing Step
> step_normalizing (C n) = (C n ** (Multi_refl, notStepCN))
>   where notStepCN: (t' : Tm ** Step (C n) t') -> Void
>         notStepCN (t' ** c) impossible
> step_normalizing (P l r) =
>   let (_ ** (ih1l,(ih1r))) = step_normalizing l
>       (_ ** (ih2l,(ih2r))) = step_normalizing r
>       ih1v = (fst nf_same_as_value) ih1r
>       ih2v = (fst nf_same_as_value) ih2r
>       n1   = lemma_get ih1v
>       n2   = lemma_get ih2v
>       (n1**p1)   = lemma_deconstruct ih1v
>       (n2**p2)   = lemma_deconstruct ih2v
>       m1 = replace p1 ih1l
>       m2 = replace p2 ih2l

>       reduction : ((P l r) ->>* (C (plus n1 n2))) =
>         let left_transform = multistep_congr_1 m1
>             right_transform =
>               let leftT = multistep_congr_2 {v=V_const n1} m2
>                   rightT = Multi_step ST_PlusConstConst Multi_refl
>                   conc2 = multi_trans {x=P (C n1) r} {y=P (C n1) (C n2)} {z=C (plus n1 n2)}
>               in conc2 leftT rightT
>             conc1 = multi_trans {x=P l r} {y=P (C n1) r} {z=C (plus n1 n2)}
>         in conc1 left_transform right_transform

>       normal_form : ((t'1 : Tm ** Step (C (plus n1 n2)) t'1) -> Void) =
>         (snd nf_same_as_value) (V_const (plus n1 n2))

>   in (C (n1 + n2) ** (reduction, normal_form))
>     where
>           lemma_get : Value v -> Nat
>           lemma_get (V_const n) = n

>           lemma_deconstruct : Value v -> (n : Nat ** v = C n)
>           lemma_deconstruct v@(V_const n) = (n ** Refl)


=== Equivalence of Big-Step and Small-Step

Having defined the operational semantics of our tiny programming
    language in two different ways (big-step and small-step), it makes
    sense to ask whether these definitions actually define the same
    thing!  They do, though it takes a little work to show it.  The
    details are left as an exercise.

==== Exercise: 3 stars (eval__multistep)

> eval__multistep: {t: Tm} -> {n: Nat} -> t >>> n -> t ->>* C n
> eval__multistep hyp = ?eval__multistep_rhs

$\square$

The key ideas in the proof can be seen in the following picture:

```
   P t1 t2 ->>            (by ST_Plus1)
   P t1' t2 ->>           (by ST_Plus1)
   P t1'' t2 ->>          (by ST_Plus1)
   ...
   P (C n1) t2 ->>        (by ST_Plus2)
   P (C n1) t2' ->>       (by ST_Plus2)
   P (C n1) t2'' ->>      (by ST_Plus2)
   ...
   P (C n1) (C n2) ->>    (by ST_PlusConstConst)
   C (n1 + n2)
```

That is, the multistep reduction of a term of the form `P t1 t2`
proceeds in three phases:

- First, we use `ST_Plus1` some number of times to reduce `t1`
 to a normal form, which must (by `nf_same_as_value`) be a
 term of the form `C n1` for some `n1`.
- Next, we use `ST_Plus2` some number of times to reduce `t2`
 to a normal form, which must again be a term of the form `C
 n2` for some `n2`.
- Finally, we use `ST_PlusConstConst` one time to reduce `P (C
 n1) (C n2)` to `C (n1 + n2)`.

To formalize this intuition, you'll need to use the congruence
    lemmas from above (you might want to review them now, so that
    you'll be able to recognize when they are useful), plus some basic
    properties of `->>*`: that it is reflexive, transitive, and
    includes `->>`.


==== Exercise: 3 stars, advanced (eval__multistep_inf)

Write a detailed informal version of the proof of `eval__multistep`

$\square$

For the other direction, we need one lemma, which establishes a
    relation between single-step reduction and big-step evaluation.

==== Exercise: 3 stars (step__eval)

> step__eval : {t, t': Tm} -> {n: Nat} ->
>     t ->> t' ->
>     t' >>> n ->
>     t >>> n
> step__eval h1 h2 = ?step__eval_rhs

$\square$

The fact that small-step reduction implies big-step evaluation is
now straightforward to prove, once it is stated correctly.

The proof proceeds by induction on the multi-step reduction
sequence that is buried in the hypothesis `normal_form_of t t'`.

Make sure you understand the statement before you start to
work on the proof.

==== Exercise: 3 stars (multistep__eval)

> multistep__eval : {t, t': Tm} ->
>   normal_form_of t t' -> (n : Nat ** (t' = C n, t >>> n))
> multistep__eval hyp = ?multistep__eval_rhs

$\square$

=== Additional Exercises

==== Exercise: 3 stars, optional (interp_tm)

Remember that we also defined big-step evaluation of terms as a
function `evalF`.  Prove that it is equivalent to the existing
semantics.  (Hint: we just proved that `eval` and `multistep` are
equivalent, so logically it doesn't matter which you choose.
One will be easier than the other, though!)

> evalF_eval : {t: Tm} -> {n: Nat} -> ((evalF t = n) <-> (t >>> n))
> evalF_eval = ?evalF_eval_rhs

$\square$

==== Exercise: 4 stars (combined_properties)

We've considered arithmetic and conditional expressions
separately.  This exercise explores how the two interact.

> data TmC : Type where
>   CC : Nat -> TmC
>   PC : TmC -> TmC -> TmC
>   TtrueC : TmC
>   TfalseC : TmC
>   TifC : TmC -> TmC -> TmC -> TmC

> data ValueC : TmC -> Type where
>   V_constC : {n: Nat} -> ValueC (CC n)
>   V_trueC : ValueC TtrueC
>   V_falseC : ValueC TfalseC

> mutual
>   infixl 6 >>->
>   (>>->) : TmC -> TmC -> Type
>   (>>->) = StepC
>
>   data StepC : TmC -> TmC -> Type where
>     ST_PlusConstConstC : PC (CC n1) (CC n2) >>-> CC (n1 + n2)
>     ST_Plus1C : t1 >>-> t1' -> PC t1 t2 >>-> PC t1' t2
>     ST_Plus2C : ValueC v1 -> t2 >>-> t2' -> PC v1 t2 >>-> PC v1 t2'
>     ST_IfTrueC : TifC TtrueC t1 t2 >>-> t1
>     ST_IfFalseC : TifC TfalseC t1 t2 >>-> t2
>     ST_IfC : t1 >>-> t1' -> TifC t1 t2 t3 >>-> TifC t1' t2 t3


Earlier, we separately proved for both plus- and if-expressions...

- that the step relation was deterministic, and

- a strong progress lemma, stating that every term is either a
  value or can take a step.

Formally prove or disprove these two properties for the combined
language.  (That is, state a theorem saying that the property
holds or does not hold, and prove your theorem.)

$\square$

  <!--

(* ################################################################# *)
(** * Small-Step Imp *)


(** Now for a more serious example: a small-step version of the Imp
    operational semantics. *)

(** The small-step reduction relations for arithmetic and
    boolean expressions are straightforward extensions of the tiny
    language we've been working up to now.  To make them easier to
    read, we introduce the symbolic notations [->>a] and [->>b] for
    the arithmetic and boolean step relations. *)

Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

(** We are not actually going to bother to define boolean
    values, since they aren't needed in the definition of [->>b]
    below (why?), though they might be if our language were a bit
    larger (why?). *)


Reserved Notation " t '/' st '->>a' t' "
                  (at level 40, st at level 39).

Inductive astep : state -> aexp -> aexp -> Prop :=
  | AS_Id : forall st i,
      AId i / st ->>a ANum (st i)
  | AS_Plus : forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st ->>a ANum (n1 + n2)
  | AS_Plus1 : forall st a1 a1' a2,
      a1 / st ->>a a1' ->
      (APlus a1 a2) / st ->>a (APlus a1' a2)
  | AS_Plus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ->>a a2' ->
      (APlus v1 a2) / st ->>a (APlus v1 a2')
  | AS_Minus : forall st n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st ->>a (ANum (minus n1 n2))
  | AS_Minus1 : forall st a1 a1' a2,
      a1 / st ->>a a1' ->
      (AMinus a1 a2) / st ->>a (AMinus a1' a2)
  | AS_Minus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ->>a a2' ->
      (AMinus v1 a2) / st ->>a (AMinus v1 a2')
  | AS_Mult : forall st n1 n2,
      (AMult (ANum n1) (ANum n2)) / st ->>a (ANum (mult n1 n2))
  | AS_Mult1 : forall st a1 a1' a2,
      a1 / st ->>a a1' ->
      (AMult a1 a2) / st ->>a (AMult a1' a2)
  | AS_Mult2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st ->>a a2' ->
      (AMult v1 a2) / st ->>a (AMult v1 a2')

    where " t '/' st '->>a' t' " := (astep st t t').

Reserved Notation " t '/' st '->>b' t' "
                  (at level 40, st at level 39).

Inductive bstep : state -> bexp -> bexp -> Prop :=
| BS_Eq : forall st n1 n2,
    (BEq (ANum n1) (ANum n2)) / st ->>b
    (if (beq_nat n1 n2) then BTrue else BFalse)
| BS_Eq1 : forall st a1 a1' a2,
    a1 / st ->>a a1' ->
    (BEq a1 a2) / st ->>b (BEq a1' a2)
| BS_Eq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st ->>a a2' ->
    (BEq v1 a2) / st ->>b (BEq v1 a2')
| BS_LtEq : forall st n1 n2,
    (BLe (ANum n1) (ANum n2)) / st ->>b
             (if (leb n1 n2) then BTrue else BFalse)
| BS_LtEq1 : forall st a1 a1' a2,
    a1 / st ->>a a1' ->
    (BLe a1 a2) / st ->>b (BLe a1' a2)
| BS_LtEq2 : forall st v1 a2 a2',
    aval v1 ->
    a2 / st ->>a a2' ->
    (BLe v1 a2) / st ->>b (BLe v1 a2')
| BS_NotTrue : forall st,
    (BNot BTrue) / st ->>b BFalse
| BS_NotFalse : forall st,
    (BNot BFalse) / st ->>b BTrue
| BS_NotStep : forall st b1 b1',
    b1 / st ->>b b1' ->
    (BNot b1) / st ->>b (BNot b1')
| BS_AndTrueTrue : forall st,
    (BAnd BTrue BTrue) / st ->>b BTrue
| BS_AndTrueFalse : forall st,
    (BAnd BTrue BFalse) / st ->>b BFalse
| BS_AndFalse : forall st b2,
    (BAnd BFalse b2) / st ->>b BFalse
| BS_AndTrueStep : forall st b2 b2',
    b2 / st ->>b b2' ->
    (BAnd BTrue b2) / st ->>b (BAnd BTrue b2')
| BS_AndStep : forall st b1 b1' b2,
    b1 / st ->>b b1' ->
    (BAnd b1 b2) / st ->>b (BAnd b1' b2)

where " t '/' st '->>b' t' " := (bstep st t t').

(** The semantics of commands is the interesting part.  We need two
    small tricks to make it work:

       - We use [SKIP] as a "command value" -- i.e., a command that
         has reached a normal form.

            - An assignment command reduces to [SKIP] (and an updated
              state).

            - The sequencing command waits until its left-hand
              subcommand has reduced to [SKIP], then throws it away so
              that reduction can continue with the right-hand
              subcommand.

       - We reduce a [WHILE] command by transforming it into a
         conditional followed by the same [WHILE]. *)

(** (There are other ways of achieving the effect of the latter
    trick, but they all share the feature that the original [WHILE]
    command needs to be saved somewhere while a single copy of the loop
    body is being reduced.) *)

Reserved Notation " t '/' st '->>' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st i a a',
      a / st ->>a a' ->
      (i ::= a) / st ->> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st ->> SKIP / (st & { i ==> n })
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ->> c1' / st' ->
      (c1 ;; c2) / st ->> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ->> c2 / st
  | CS_IfTrue : forall st c1 c2,
      IFB BTrue THEN c1 ELSE c2 FI / st ->> c1 / st
  | CS_IfFalse : forall st c1 c2,
      IFB BFalse THEN c1 ELSE c2 FI / st ->> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b / st ->>b b' ->
          IFB b THEN c1 ELSE c2 FI / st
      ->> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
          (WHILE b DO c1 END) / st
      ->> (IFB b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st

  where " t '/' st '->>' t' '/' st' " := (cstep (t,st) (t',st')).

(* ################################################################# *)
(** * Concurrent Imp *)

(** Finally, to show the power of this definitional style, let's
    enrich Imp with a new form of command that runs two subcommands in
    parallel and terminates when both have terminated.  To reflect the
    unpredictability of scheduling, the actions of the subcommands may
    be interleaved in any order, but they share the same memory and
    can communicate by reading and writing the same variables. *)

Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  (* New: *)
  | CPar : com -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity).
Notation "'PAR' c1 'WITH' c2 'END'" :=
  (CPar c1 c2) (at level 80, right associativity).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
    (* Old part *)
  | CS_AssStep : forall st i a a',
      a / st ->>a a' ->
      (i ::= a) / st ->> (i ::= a') / st
  | CS_Ass : forall st i n,
      (i ::= (ANum n)) / st ->> SKIP / st & { i ==> n }
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st ->> c1' / st' ->
      (c1 ;; c2) / st ->> (c1' ;; c2) / st'
  | CS_SeqFinish : forall st c2,
      (SKIP ;; c2) / st ->> c2 / st
  | CS_IfTrue : forall st c1 c2,
      (IFB BTrue THEN c1 ELSE c2 FI) / st ->> c1 / st
  | CS_IfFalse : forall st c1 c2,
      (IFB BFalse THEN c1 ELSE c2 FI) / st ->> c2 / st
  | CS_IfStep : forall st b b' c1 c2,
      b /st ->>b b' ->
          (IFB b THEN c1 ELSE c2 FI) / st
      ->> (IFB b' THEN c1 ELSE c2 FI) / st
  | CS_While : forall st b c1,
          (WHILE b DO c1 END) / st
      ->> (IFB b THEN (c1;; (WHILE b DO c1 END)) ELSE SKIP FI) / st
    (* New part: *)
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st ->> c1' / st' ->
      (PAR c1 WITH c2 END) / st ->> (PAR c1' WITH c2 END) / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st ->> c2' / st' ->
      (PAR c1 WITH c2 END) / st ->> (PAR c1 WITH c2' END) / st'
  | CS_ParDone : forall st,
      (PAR SKIP WITH SKIP END) / st ->> SKIP / st
  where " t '/' st '->>' t' '/' st' " := (cstep (t,st) (t',st')).

Definition cmultistep := multi cstep.

Notation " t '/' st '->>*' t' '/' st' " :=
   (multi cstep  (t,st) (t',st'))
   (at level 40, st at level 39, t' at level 39).

(** Among the many interesting properties of this language is the fact
    that the following program can terminate with the variable [X] set
    to any value. *)

Definition par_loop : com :=
  PAR
    Y ::= 1
  WITH
    WHILE Y = 0 DO
      X ::= X + 1
    END
  END.

(** In particular, it can terminate with [X] set to [0]: *)

Example par_loop_example_0:
  exists st',
       par_loop / { ==> 0 }  ->>* SKIP / st'
    /\ st' X = 0.
Proof.
  eapply ex_intro. split.
  unfold par_loop.
  eapply multi_step. apply CS_Par1.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

(** It can also terminate with [X] set to [2]: *)

Example par_loop_example_2:
  exists st',
       par_loop / { ==> 0 } ->>* SKIP / st'
    /\ st' X = 2.
Proof.
  eapply ex_intro. split.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.

  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfTrue.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_AssStep. apply AS_Plus.
  eapply multi_step. apply CS_Par2. apply CS_SeqStep.
    apply CS_Ass.

  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_SeqFinish.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  eapply multi_refl.
  reflexivity. Qed.

(** More generally... *)

(** **** Exercise: 3 stars, optional (par_body_n__Sn)  *)
Lemma par_body_n__Sn : forall n st,
  st X = n /\ st Y = 0 ->
  par_loop / st ->>* par_loop / st & { X ==> S n}.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (par_body_n)  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ->>*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** ... the above loop can exit with [X] having any value
    whatsoever. *)

Theorem par_loop_any_X:
  forall n, exists st',
    par_loop / { ==> 0 } ->>*  SKIP / st'
    /\ st' X = n.
Proof.
  intros n.
  destruct (par_body_n n { ==> 0 }).
    split; unfold t_update; reflexivity.

  rename x into st.
  inversion H as [H' [HX HY]]; clear H.
  exists (st & { Y ==> 1 }). split.
  eapply multi_trans with (par_loop,st). apply H'.
  eapply multi_step. apply CS_Par1. apply CS_Ass.
  eapply multi_step. apply CS_Par2. apply CS_While.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq1. apply AS_Id. rewrite t_update_eq.
  eapply multi_step. apply CS_Par2. apply CS_IfStep.
    apply BS_Eq. simpl.
  eapply multi_step. apply CS_Par2. apply CS_IfFalse.
  eapply multi_step. apply CS_ParDone.
  apply multi_refl.

  rewrite t_update_neq. assumption. intro X; inversion X.
Qed.

End CImp.

(* ################################################################# *)
(** * A Small-Step Stack Machine *)

(** Our last example is a small-step semantics for the stack machine
    example from the [Imp] chapter of _Logical Foundations_. *)

Definition stack := list nat.
Definition prog  := list sinstr.

Inductive stack_step : state -> prog * stack -> prog * stack -> Prop :=
  | SS_Push : forall st stk n p',
    stack_step st (SPush n :: p', stk)      (p', n :: stk)
  | SS_Load : forall st stk i p',
    stack_step st (SLoad i :: p', stk)      (p', st i :: stk)
  | SS_Plus : forall st stk n m p',
    stack_step st (SPlus :: p', n::m::stk)  (p', (m+n)::stk)
  | SS_Minus : forall st stk n m p',
    stack_step st (SMinus :: p', n::m::stk) (p', (m-n)::stk)
  | SS_Mult : forall st stk n m p',
    stack_step st (SMult :: p', n::m::stk)  (p', (m*n)::stk).

Theorem stack_step_deterministic : forall st,
  deterministic (stack_step st).
Proof.
  unfold deterministic. intros st x y1 y2 H1 H2.
  induction H1; inversion H2; reflexivity.
Qed.

Definition stack_multistep st := multi (stack_step st).

(** **** Exercise: 3 stars, advanced (compiler_is_correct)  *)
(** Remember the definition of [compile] for [aexp] given in the
    [Imp] chapter of _Logical Foundations_. We want now to
    prove [compile] correct with respect to the stack machine.

    State what it means for the compiler to be correct according to
    the stack machine small step semantics and then prove it. *)

Definition compiler_is_correct_statement : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem compiler_is_correct : compiler_is_correct_statement.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

-->
