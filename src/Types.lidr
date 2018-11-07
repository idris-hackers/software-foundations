= Types

== Types: Type Systems

> module Types
> import Smallstep
> %hide Smallstep.(->>)
> %hide Smallstep.Tm
> %hide Smallstep.Ttrue
> %hide Smallstep.Tfalse



> %access public export
> %default total


Our next major topic is _type systems_ -- static program
analyses that classify expressions according to the "shapes" of
their results.  We'll begin with a typed version of the simplest
imaginable language, to introduce the basic ideas of types and
typing rules and the fundamental theorems about type systems:
_type preservation_ and _progress_.  In chapter `Stlc` we'll move
on to the _simply typed lambda-calculus_, which lives at the core
of every modern functional programming language (including
Idris!).

== Typed Arithmetic Expressions

To motivate the discussion of type systems, let's begin as
usual with a tiny toy language.  We want it to have the potential
for programs to go wrong because of runtime type errors, so we
need something a tiny bit more complex than the language of
constants and addition that we used in chapter `Smallstep`: a
single kind of data (e.g., numbers) is too simple, but just two
kinds (numbers and booleans) gives us enough material to tell an
interesting story.

The language definition is completely routine.

=== Syntax

Here is the syntax, informally:

```
    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t
```

And here it is formally:

> data Tm : Type where
>   Ttrue     : Tm
>   Tfalse    : Tm
>   Tif       : Tm -> Tm -> Tm -> Tm
>   Tzero     : Tm
>   Tsucc     : Tm -> Tm
>   Tpred     : Tm -> Tm
>   Tiszero   : Tm -> Tm

_Values_ are `true`, `false`, and numeric values...

> data Bvalue : Tm -> Type where
>   Bv_true : Bvalue Ttrue
>   Bv_false : Bvalue Tfalse
>
> data Nvalue : Tm -> Type where
>   Nv_zero : Nvalue Tzero
>   Nv_succ : {t: Tm} -> Nvalue t -> Nvalue (Tsucc t)
>
> data Value : Tm -> Type where
>   V_bool : Bvalue t -> Value t
>   V_nat : Nvalue t -> Value t

=== Operational Semantics

Here is the single-step relation, first informally...

\[
  \begin{prooftree}
    \infer0[\idr{ST_IfTrue}]{\idr{if true then t1 else t2 ->> t1}}
  \end{prooftree}
  \newline
\]

\[
  \begin{prooftree}
    \infer0[\idr{ST_IfFalse}]{\idr{if false then t1 else t2 ->> t2}}
  \end{prooftree}
  \newline
\]

\[
  \begin{prooftree}
    \hypo{\idr{t1 ->> t1'}}
    \infer1[\idr{ST_If}]{\idr{if t1 then t2 else t3 ->> if t1' then t2 else t3}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{t1 ->> t1'}}
    \infer1[\idr{ST_Succ}]{\idr{succ t1 ->> succ t1'}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \infer0[\idr{ST_PredZero}]{\idr{pred 0 ->> 0}}
  \end{prooftree}
  \newline
\]

\[
  \begin{prooftree}
    \hypo{\idr{numeric value v1}}
    \infer1[\idr{ST_PredSucc}]{\idr{pred (succ v1) ->> v1}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{t1 ->> t1'}}
    \infer1[\idr{ST_Pred}]{\idr{pred t1 ->> pred t1'}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \infer0[\idr{ST_IszeroZero}]{\idr{iszero 0 ->> true}}
  \end{prooftree}
  \newline
\]

\[
  \begin{prooftree}
    \hypo{\idr{numeric value v1}}
    \infer1[\idr{ST_IszeroSucc}]{\idr{iszero (succ v1) ->> false}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{t1 ->> t1'}}
    \infer1[\idr{ST_Iszero}]{\idr{iszero t1 ->> iszero t1'}}
  \end{prooftree}
\]

... and then formally:


> mutual
>   infixl 6 ->>
>   (->>) : Tm -> Tm -> Type
>   (->>) = Types.Step
>
>   data Step     : Tm -> Tm -> Type where
>     ST_IfTrue   : {t1, t2: Tm} -> Tif Ttrue t1 t2 ->> t1
>     ST_IfFalse  : {t1, t2: Tm} -> Tif Tfalse t1 t2 ->> t2
>     ST_If       : {t1, t2, t3, t1': Tm} -> t1 ->> t1' -> Tif t1 t2 t3 ->> Tif t1' t2 t3
>     ST_Succ     : {t1, t1': Tm} -> t1 ->> t1' -> Tsucc t1 ->> Tsucc t1'
>     ST_PredZero : Tpred tzero ->> tzero
>     ST_PredSucc : {t1 :Tm} -> Nvalue t1 -> Tpred (Tsucc t1) ->> t1
>     ST_Pred     : {t1, t1': Tm} -> t1 ->> t1' -> Tpred t1 ->> Tpred t1'
>     ST_IszeroZero : Tiszero Tzero ->> Ttrue
>     ST_IszeroSucc : {t1: Tm} -> Nvalue t1 -> Tiszero (Tsucc t1) ->> Tfalse
>     ST_Iszero   : {t1, t1': Tm} -> t1 ->> t1' -> Tiszero t1 ->> Tiszero t1'


Notice that the `step` relation doesn't care about whether
expressions make global sense -- it just checks that the operation
in the _next_ reduction step is being applied to the right kinds
of operands.  For example, the term `succ true` (i.e.,
`tsucc ttrue` in the formal syntax) cannot take a step, but the
almost as obviously nonsensical term

       succ (if true then true else true)

can take a step (once, before becoming stuck).

=== Normal Forms and Values

The first interesting thing to notice about this `step` relation
is that the strong progress theorem from the `Smallstep` chapter
fails here.  That is, there are terms that are normal forms (they
can't take a step) but not values (because we have not included
them in our definition of possible "results of reduction").  Such
terms are _stuck_.

> step_normal_form : (t : Tm) -> Type
> step_normal_form = normal_form Types.Step

> stuck : (t : Tm) -> Type
> stuck t = (step_normal_form t, Not (Value t))

==== Exercise: 2 stars (some_term_is_stuck)

> some_term_is_stuck : (t ** stuck t)
> some_term_is_stuck = ?some_term_is_stuck_rhs

$\square$

However, although values and normal forms are _not_ the same in this
language, the set of values is included in the set of normal
forms.  This is important because it shows we did not accidentally
define things so that some value could still take a step.

==== Exercise: 3 stars (value_is_nf)

> value_is_nf : {t: Tm} -> Value t -> step_normal_form t
> value_is_nf = ?value_is_nf_rhs

$\square$

==== Exercise: 3 stars, optional (step_deterministic)

Use `value_is_nf` to show that the `step` relation is also
    deterministic.

> step_deterministic : deterministic step
> step_deterministic = ?step_deterministic_rhs

$\square$

== Typing

The next critical observation is that, although this
language has stuck terms, they are always nonsensical, mixing
booleans and numbers in a way that we don't even _want_ to have a
meaning.  We can easily exclude such ill-typed terms by defining a
_typing relation_ that relates terms to the types (either numeric
or boolean) of their final results.

> data Ty : Type where
>   TBool : Ty
>   TNat  : Ty

In informal notation, the typing relation is often written
`|- t \in T` and pronounced "`t` has type `T`."  The `|-` symbol
is called a "turnstile."  Below, we're going to see richer typing
relations where one or more additional "context" arguments are
written to the left of the turnstile.  For the moment, the context
is always empty.

\[
  \begin{prooftree}
    \infer0[\idr{T_True}]{\idr{|- true \\in Bool}}
  \end{prooftree}
  \newline
\]

\[
  \begin{prooftree}
    \infer0[\idr{T_False}]{\idr{|- false \\in Bool}}
  \end{prooftree}
  \newline
\]

\[
  \begin{prooftree}
    \hypo{\idr{|- t1 \\in Bool}}
    \hypo{\idr{|- t2 \\in T}}
    \hypo{\idr{|- t3 \\in T}}
    \infer3[\idr{T_If}]{\idr{|- if t1 then t2 else t3 \\in T}}
  \end{prooftree}
  \newline
\]

\[
  \begin{prooftree}
    \infer0[\idr{T_Zero}]{\idr{|- 0 \\in Nat}}
  \end{prooftree}
  \newline
\]

\[
  \begin{prooftree}
    \hypo{\idr{|- t1 \\in Nat}}
    \infer1[\idr{T_Succ}]{\idr{|- succ t1 \\in Nat}}
  \end{prooftree}
  \newline
\]

\[
  \begin{prooftree}
    \hypo{\idr{|- t1 \\in Nat}}
    \infer1[\idr{T_Pred}]{\idr{|- pred t1 \\in Nat}}
  \end{prooftree}
  \newline
\]

\[
  \begin{prooftree}
    \hypo{\idr{|- t1 \\in Nat}}
    \infer1[\idr{T_IsZero}]{\idr{|- iszero t1 \\in Bool}}
  \end{prooftree}
  \newline
\]

> syntax "|-" [p] ":" [q] "."= Has_type p q

> data Has_type : Tm -> Ty -> Type where
>   T_True : |- Ttrue : TBool .
>   T_False : |- Tfalse : TBool .
>   T_If : {t1, t2, t3: Tm} -> {T: Ty} ->
>       |- t1 : TBool . ->
>       |- t2 : T . ->
>       |- t3 : T . ->
>       |- (Tif t1 t2 t3) : T .
>   T_Zero : |- Tzero : TNat .
>   T_Succ : {t1 : Tm} ->
>       |- t1 : TNat . ->
>       |- (Tsucc t1) : TNat .
>   T_Pred : {t1 : Tm} ->
>       |- t1 : TNat . ->
>       |- (Tpred t1) : TNat .
>   T_Iszero : {t1 : Tm} ->
>       |- t1 : TNat . ->
>       |- (Tiszero t1) : TBool .

> has_type_1 : |- (Tif Tfalse Tzero (Tsucc Tzero)) : TNat .
> has_type_1 = T_If (T_False) (T_Zero) (T_Succ T_Zero)

It's important to realize that the typing relation is a
_conservative_ (or _static_) approximation: it does not consider
what happens when the term is reduced -- in particular, it does
not calculate the type of its normal form.

> has_type_not : Not ( |- (Tif Tfalse Tzero Ttrue) : TBool . )
> has_type_not (T_If (T_False) (T_Zero) (T_True)) impossible

==== Exercise: 1 star, optional (succ_hastype_nat__hastype_nat)

> succ_hastype_nat__hastype_nat : {t : Tm} ->
>   |- (Tsucc t) : TNat . -> |- t : TNat .
> succ_hastype_nat__hastype_nat = ?succ_hastype_nat__hastype_nat_rhs

$\square$

=== Canonical forms

The following two lemmas capture the fundamental property that the
definitions of boolean and numeric values agree with the typing
relation.

> bool_canonical : {t: Tm} -> |- t : TBool . -> Value t -> Bvalue t
> bool_canonical {t} ht v =
>   case v of
>     V_bool b => b
>     V_nat n => void (lemma n ht)
>   where lemma : {t:Tm} -> Nvalue t -> Not ( |- t : TBool . )
>         lemma {t=Tzero} n T_Zero impossible
>         lemma {t=Tsucc n'} n (T_Succ n') impossible

> nat_canonical : {t: Tm} -> |- t : TNat . -> Value t -> Nvalue t
> nat_canonical {t} ht v =
>   case v of
>     V_nat n => n
>     V_bool b => void (lemma b ht)
>   where lemma : {t:Tm} -> Bvalue t -> Not ( |- t : TNat . )
>         lemma {t=Ttrue} n T_True impossible
>         lemma {t=Tfalse} n T_False impossible

=== Progress

The typing relation enjoys two critical properties.  The first is
that well-typed normal forms are not stuck -- or conversely, if a
term is well typed, then either it is a value or it can take at
least one step.  We call this _progress_.

> progress : {t: Tm} -> {ty: Ty} -> |- t : ty . -> Either (Value t) (t' ** t ->> t')

==== Exercise: 3 stars (finish_progress)

Complete the formal proof of the `progress` property.  (Make sure
    you understand the parts we've given of the informal proof in the
    following exercise before starting -- this will save you a lot of
    time.)

> progress {t=Tif t1 t2 t3} (T_If h1 h2 h3) =
>   case progress h1 of
>     Left hypL => Right (
>        let h1 = bool_canonical h1 hypL
>        in case t1 of
>           Ttrue => (t2 ** ST_IfTrue)
>           Tfalse => (t3 ** ST_IfFalse)
>     )
>     Right (t' ** hr) => Right ((Tif t' t2 t3) ** ST_If hr)
> progress t = ?progress_rhs

$\square$

==== Exercise: 3 stars, advanced (finish_progress_informal)

Complete the corresponding informal proof:

_Theorem_: If `|- t \in T`, then either `t` is a value or else
    `t ==> t'` for some `t'`.

_Proof_: By induction on a derivation of `|- t \in T`.

- If the last rule in the derivation is `T_If`, then `t = if t1
  then t2 else t3`, with `|- t1 \in Bool`, `|- t2 \in T` and `|- t3
  \in T`.  By the IH, either `t1` is a value or else `t1` can step
  to some `t1'`.

      - If `t1` is a value, then by the canonical forms lemmas
        and the fact that `|- t1 \in Bool` we have that `t1`
        is a `bvalue` -- i.e., it is either `true` or `false`.
        If `t1 = true`, then `t` steps to `t2` by `ST_IfTrue`,
        while if `t1 = false`, then `t` steps to `t3` by
        `ST_IfFalse`.  Either way, `t` can step, which is what
        we wanted to show.

      - If `t1` itself can take a step, then, by `ST_If`, so can
        `t`.

$\square$

This theorem is more interesting than the strong progress theorem
that we saw in the `Smallstep` chapter, where _all_ normal forms
were values.  Here a term can be stuck, but only if it is ill
typed.


=== Type Preservation

The second critical property of typing is that, when a well-typed
term takes a step, the result is also a well-typed term.

> preservation : {t, t': Tm} -> {T: Ty} ->
>  |- t : T . -> t ->> t' -> |- t' : T .

==== Exercise: 2 stars (finish_preservation)

> preservation {t=Tif t1 t2 t3} {t'} (T_If h1 h2 h3) he =
>   case he of
>     ST_IfTrue => h2
>     ST_IfFalse => h3
>     ST_If hyp =>
>       let indHyp = preservation h1 hyp
>       in T_If indHyp h2 h3
>     ST_Succ hyp impossible
>     ST_PredZero impossible
>     ST_PredSucc hyp impossible
>     ST_Pred hyp impossible
>     ST_IszeroZero impossible
>     ST_IszeroSucc hyp impossible
>     ST_Iszero hyp impossible
> preservation t he = ?preservation_rhs

Complete the formal proof of the `preservation` property.  (Again,
    make sure you understand the informal proof fragment in the
    following exercise first.)

$\square$

==== Exercise: 3 stars, advanced (finish_preservation_informal)

Complete the following informal proof:

_Theorem_: If `|- t \in T` and `t ==> t'`, then `|- t' \in T`.

_Proof_: By induction on a derivation of `|- t \in T`.

- If the last rule in the derivation is `T_If`, then `t = if t1
  then t2 else t3`, with `|- t1 \in Bool`, `|- t2 \in T` and `|- t3
  \in T`.

  Inspecting the rules for the small-step reduction relation and
  remembering that `t` has the form `if ...`, we see that the
  only ones that could have been used to prove `t ==> t'` are
  `ST_IfTrue`, `ST_IfFalse`, or `ST_If`.

     - If the last rule was `ST_IfTrue`, then `t' = t2`.  But we
       know that `|- t2 \in T`, so we are done.

     - If the last rule was `ST_IfFalse`, then `t' = t3`.  But we
       know that `|- t3 \in T`, so we are done.

     - If the last rule was `ST_If`, then `t' = if t1' then t2
       else t3`, where `t1 ==> t1'`.  We know `|- t1 \in Bool` so,
       by the IH, `|- t1' \in Bool`.  The `T_If` rule then gives us
       `|- if t1' then t2 else t3 \in T`, as required.

$\square$

==== Exercise: 3 stars (preservation_alternate_proof)

Now prove the same property again by induction on the
_evaluation_ derivation instead of on the typing derivation.
Begin by carefully reading and thinking about the first few
lines of the above proofs to make sure you understand what
each one is doing.  The set-up for this proof is similar, but
not exactly the same.

> preservation' : {t, t': Tm} -> {T: Ty} ->
>  |- t : T . -> t ->> t' -> |- t' : T .
> preservation' h1 h2 = ?preservation'_rhs

$\square$

The preservation theorem is often called _subject reduction_,
because it tells us what happens when the "subject" of the typing
relation is reduced.  This terminology comes from thinking of
typing statements as sentences, where the term is the subject and
the type is the predicate.

=== Type Soundness

Putting progress and preservation together, we see that a
well-typed term can never reach a stuck state.

> mutual
>   infixl 6 ->>*
>   (->>*) : Tm -> Tm -> Type
>   (->>*) = multistep

>   multistep : Tm -> Tm -> Type
>   multistep = Multi Step

> soundness : {t, t': Tm} -> {T: Ty} ->
>   |- t : T . ->
>   t ->>* t' ->
>   Not (stuck t')
> soundness ht Multi_refl (sl,sr) =
>   case progress ht of
>     Left hl => sr hl
>     Right hr => sl hr
> soundness ht (Multi_step single multi) stuck =
>   let ht'    = preservation ht single
>       indHyp = soundness ht' multi
>   in indHyp stuck

  <!--

(* ################################################################# *)
(** * Aside: the `normalize` Tactic *)

(** When experimenting with definitions of programming languages
    in Coq, we often want to see what a particular concrete term steps
    to -- i.e., we want to find proofs for goals of the form `t ==>*
    t'`, where `t` is a completely concrete term and `t'` is unknown.
    These proofs are quite tedious to do by hand.  Consider, for
    example, reducing an arithmetic expression using the small-step
    relation `astep`. *)

Module NormalizePlayground.
Import Smallstep.

Example step_example1 :
  (P (C 3) (P (C 3) (C 4)))
  ==>* (C 10).
Proof.
  apply multi_step with (P (C 3) (C 7)).
    apply ST_Plus2.
      apply v_const.
      apply ST_PlusConstConst.
  apply multi_step with (C 10).
    apply ST_PlusConstConst.
  apply multi_refl.
Qed.

(** The proof repeatedly applies `multi_step` until the term reaches a
    normal form.  Fortunately The sub-proofs for the intermediate
    steps are simple enough that `auto`, with appropriate hints, can
    solve them. *)

Hint Constructors step value.
Example step_example1' :
  (P (C 3) (P (C 3) (C 4)))
  ==>* (C 10).
Proof.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.

(** The following custom `Tactic Notation` definition captures this
    pattern.  In addition, before each step, we print out the current
    goal, so that we can follow how the term is being reduced. *)

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.

Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            ` (eauto 10; fail) | (instantiate; simpl)`);
  apply multi_refl.

Example step_example1'' :
  (P (C 3) (P (C 3) (C 4)))
  ==>* (C 10).
Proof.
  normalize.
  (* The `print_goal` in the `normalize` tactic shows
     a trace of how the expression reduced...
         (P (C 3) (P (C 3) (C 4)) ==>* C 10)
         (P (C 3) (C 7) ==>* C 10)
         (C 10 ==>* C 10)
  *)
Qed.

(** The `normalize` tactic also provides a simple way to calculate the
    normal form of a term, by starting with a goal with an existentially
    bound variable. *)

Example step_example1''' : exists e',
  (P (C 3) (P (C 3) (C 4)))
  ==>* e'.
Proof.
  eapply ex_intro. normalize.
(* This time, the trace is:
       (P (C 3) (P (C 3) (C 4)) ==>* ?e')
       (P (C 3) (C 7) ==>* ?e')
       (C 10 ==>* ?e')
   where ?e' is the variable ``guessed'' by eapply. *)
Qed.


(** **** Exercise: 1 star (normalize_ex)  *)
Theorem normalize_ex : exists e',
  (P (C 3) (P (C 2) (C 1)))
  ==>* e'.
Proof.
  (* FILL IN HERE *) Admitted.
(** `` *)

(** **** Exercise: 1 star, optional (normalize_ex')  *)
(** For comparison, prove it using `apply` instead of `eapply`. *)

Theorem normalize_ex' : exists e',
  (P (C 3) (P (C 2) (C 1)))
  ==>* e'.
Proof.
  (* FILL IN HERE *) Admitted.
(** `` *)

End NormalizePlayground.

Tactic Notation "print_goal" :=
  match goal with |- ?x => idtac x end.
Tactic Notation "normalize" :=
  repeat (print_goal; eapply multi_step ;
            ` (eauto 10; fail) | (instantiate; simpl)`);
  apply multi_refl.

 -->

=== Additional Exercises

==== Exercise: 2 stars, recommended (subject_expansion)

Having seen the subject reduction property, one might
wonder whether the opposity property -- subject _expansion_ --
also holds.  That is, is it always the case that, if `t ==> t'`
and `|- t' \in T`, then `|- t \in T`?  If so, prove it.  If
not, give a counter-example.  (You do not need to prove your
counter-example in Idris, but feel free to do so.)

$\square$

==== Exercise: 2 stars (variation1)

Suppose, that we add this new rule to the typing relation:

```idris
       T_SuccBool : {t: Tm} ->
           HasType t TBool ->
           |- Tsucc t . TBool
```

Which of the following properties remain true in the presence of
this rule?  For each one, write either "remains true" or
else "becomes false." If a property becomes false, give a
counterexample.
  - Determinism of `step`

  - Progress

  - Preservation

$\square$

==== Exercise: 2 stars (variation2)

Suppose, instead, that we add this new rule to the `step` relation:

```idris
      ST_Funny1 : {t2, t3: Tm} ->
           (tif ttrue t2 t3) ->>* t3
```

Which of the above properties become false in the presence of
this rule?  For each one that does, give a counter-example.

$\square$

==== Exercise: 2 stars, optional (variation3)

Suppose instead that we add this rule:

```idris
      ST_Funny2 : {t1, t2, t2', t3: Tm} ->
           t2 ->>* t2' ->
           (tif t1 t2 t3) ->>* (tif t1 t2' t3)
```

Which of the above properties become false in the presence of
this rule?  For each one that does, give a counter-example.

$\square$

==== Exercise: 2 stars, optional (variation4)

Suppose instead that we add this rule:

```idris
      ST_Funny3 :
          (tpred tfalse) ->>* (tpred (tpred tfalse))
```

Which of the above properties become false in the presence of
this rule?  For each one that does, give a counter-example.

$\square$

==== Exercise: 2 stars, optional (variation5)

Suppose instead that we add this rule:

```idris
      T_Funny4 :
            |- Tzero . TBool
```

Which of the above properties become false in the presence of
this rule?  For each one that does, give a counter-example.

$\square$

==== Exercise: 2 stars, optional (variation6)

Suppose instead that we add this rule:

```idris
      T_Funny5 :
            |- Tpred Tzero . TBool
```

Which of the above properties become false in the presence of
this rule?  For each one that does, give a counter-example.

$\square$

==== Exercise: 3 stars, optional (more_variations)

Make up some exercises of your own along the same lines as
the ones above.  Try to find ways of selectively breaking
properties -- i.e., ways of changing the definitions that
break just one of the properties and leave the others alone.

$\square$

==== Exercise: 1 star (remove_predzero)

The reduction rule `ST_PredZero` is a bit counter-intuitive: we
might feel that it makes more sense for the predecessor of zero to
be undefined, rather than being defined to be zero.  Can we
achieve this simply by removing the rule from the definition of
`step`?  Would doing so create any problems elsewhere?

$\square$

==== Exercise: 4 stars, advanced (prog_pres_bigstep)

Suppose our evaluation relation is defined in the big-step style.
State appropriate analogs of the progress and preservation
properties. (You do not need to prove them.)

Can you see any limitations of either of your properties?
Do they allow for nonterminating commands?
Why might we prefer the small-step semantics for stating
preservation and progress?

$\square$
