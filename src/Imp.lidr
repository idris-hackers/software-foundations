= Imp : Simple Imperative Programs

> module Imp

> import Logic

In this chapter, we begin a new direction that will continue for the rest of the
course. Up to now most of our attention has been focused on various aspects of
Idris itself, while from now on we'll mostly be using Idris to formalize other
things. (We'll continue to pause from time to time to introduce a few additional
aspects of Idris.)

Our first case study is a _simple imperative programming language_ called Imp,
embodying a tiny core fragment of conventional mainstream languages such as C
and Java. Here is a familiar mathematical function written in Imp.

```
     Z ::= X;;
     Y ::= 1;;
     WHILE not (Z == 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END
```

This chapter looks at how to define the _syntax_ and _semantics_ of Imp; the
chapters that follow develop a theory of _program equivalence_ and introduce
_Hoare Logic_, a widely used logic for reasoning about imperative programs.

> import Maps

> %hide (\\)

> %default total
> %access public export


== Arithmetic and Boolean Expressions

We'll present Imp in three parts: first a core language of _arithmetic and
boolean expressions_, then an extension of these expressions with _variables_,
and finally a language of _commands_ including assignment, conditions,
sequencing, and loops.


=== Syntax

These two definitions specify the _abstract syntax_ of arithmetic and boolean
expressions.

> data AExp0 : Type where
>   ANum0 : Nat -> AExp0
>   APlus0 : AExp0 -> AExp0 -> AExp0
>   AMinus0 : AExp0 -> AExp0 -> AExp0
>   AMult0 : AExp0 -> AExp0 -> AExp0
>
> data BExp0 : Type where
>   BTrue0 : BExp0
>   BFalse0 : BExp0
>   BEq0 : AExp0 -> AExp0 -> BExp0
>   BLe0 : AExp0 -> AExp0 -> BExp0
>   BNot0 : BExp0 -> BExp0
>   BAnd0 : BExp0 -> BExp0 -> BExp0

In this chapter, we'll elide the translation from the concrete syntax that a
programmer would actually write to these abstract syntax trees — the process
that, for example, would translate the string \idr{"1+2*3"} to the AST

```idris
      APlus0 (ANum0 1) (AMult0 (ANum0 2) (ANum0 3))
```

The optional chapter `ImpParser` develops a simple implementation of a lexical
analyzer and parser that can perform this translation. You do _not_ need to
understand that chapter to understand this one, but if you haven't taken a
course where these techniques are covered (e.g., a compilers course) you may
want to skim it.

For comparison, here's a conventional BNF (Backus-Naur Form) grammar defining
the same abstract syntax:

```
    a ::= Nat
        | a + a
        | a - a
        | a * a

    b ::= True
        | False
        | a = a
        | a ≤ a
        | not b
        | b and b
```

Compared to the Idris version above...

  - The BNF is more informal — for example, it gives some suggestions about the
    surface syntax of expressions (like the fact that the addition operation is
    written \idr{+} and is an infix symbol) while leaving other aspects of
    lexical analysis and parsing (like the relative precedence of \idr{+},
    \idr{-}, and \idr{*}, the use of parens to explicitly group subexpressions,
    etc.) unspecified. Some additional information (and human intelligence)
    would be required to turn this description into a formal definition, for
    example when implementing a compiler.

    The Idris version consistently omits all this information and concentrates
    on the abstract syntax only.

  - On the other hand, the BNF version is lighter and easier to read. Its
    informality makes it flexible, a big advantage in situations like
    discussions at the blackboard, where conveying general ideas is more
    important than getting every detail nailed down precisely.

    Indeed, there are dozens of BNF-like notations and people switch freely
    among them, usually without bothering to say which form of BNF they're using
    because there is no need to: a rough-and-ready informal understanding is all
    that's important.

It's good to be comfortable with both sorts of notations: informal ones for
communicating between humans and formal ones for carrying out implementations
and proofs.


=== Evaluation

_Evaluating_ an arithmetic expression produces a number.

> aeval0 : (a : AExp0) -> Nat
> aeval0 (ANum0 n) = n
> aeval0 (APlus0 a1 a2) = (aeval0 a1) + (aeval0 a2)
> aeval0 (AMinus0 a1 a2) = (aeval0 a1) `minus` (aeval0 a2)
> aeval0 (AMult0 a1 a2) = (aeval0 a1) * (aeval0 a2)

> test_aeval1 : aeval0 (APlus0 (ANum0 2) (ANum0 2)) = 4
> test_aeval1 = Refl

Similarly, evaluating a boolean expression yields a boolean.

> beval0 : (b : BExp0) -> Bool
> beval0 BTrue0 = True
> beval0 BFalse0 = False
> beval0 (BEq0 a1 a2) = (aeval0 a1) == (aeval0 a2)
> beval0 (BLe0 a1 a2) = lte (aeval0 a1) (aeval0 a2)
> beval0 (BNot0 b1) = not (beval0 b1)
> beval0 (BAnd0 b1 b2) = (beval0 b1) && (beval0 b2)

=== Optimization

We haven't defined very much yet, but we can already get some mileage out of the
definitions. Suppose we define a function that takes an arithmetic expression
and slightly simplifies it, changing every occurrence of \idr{0+e} (i.e.,
\idr{(APlus0 (ANum0 0) e}) into just \idr{e}.

> optimize_0plus : (a : AExp0) -> AExp0
> optimize_0plus (ANum0 n) = ANum0 n
> optimize_0plus (APlus0 (ANum0 Z) e2) =
>   optimize_0plus e2
> optimize_0plus (APlus0 e1 e2) =
>   APlus0 (optimize_0plus e1) (optimize_0plus e2)
> optimize_0plus (AMinus0 e1 e2) =
>   AMinus0 (optimize_0plus e1) (optimize_0plus e2)
> optimize_0plus (AMult0 e1 e2) =
>   AMult0 (optimize_0plus e1) (optimize_0plus e2)

To make sure our optimization is doing the right thing we can test it on some
examples and see if the output looks OK.

> test_optimize_0plus :
>   optimize_0plus (APlus0 (ANum0 2)
>                         (APlus0 (ANum0 0)
>                                (APlus0 (ANum0 0) (ANum0 1))))
>   = APlus0 (ANum0 2) (ANum0 1)

But if we want to be sure the optimization is correct — i.e., that evaluating an
optimized expression gives the same result as the original — we should prove it.

> optimize_0plus_sound : aeval0 (optimize_0plus a) = aeval0 a
> optimize_0plus_sound {a=ANum0 _} = Refl
> optimize_0plus_sound {a=APlus0 (ANum0 Z) y} =
>   optimize_0plus_sound {a=y}
> optimize_0plus_sound {a=APlus0 (ANum0 (S k)) y} =
>   cong {f=\x=>S(k+x)} $ optimize_0plus_sound {a=y}
> optimize_0plus_sound {a=APlus0 (APlus0 x z) y} =
>   rewrite optimize_0plus_sound {a=APlus0 x z} in
>   rewrite optimize_0plus_sound {a=y} in
>   Refl
> optimize_0plus_sound {a=APlus0 (AMinus0 x z) y} =
>   rewrite optimize_0plus_sound {a=x} in
>   rewrite optimize_0plus_sound {a=y} in
>   rewrite optimize_0plus_sound {a=z} in
>   Refl
> optimize_0plus_sound {a=APlus0 (AMult0 x z) y} =
>   rewrite optimize_0plus_sound {a=x} in
>   rewrite optimize_0plus_sound {a=y} in
>   rewrite optimize_0plus_sound {a=z} in
>   Refl
> optimize_0plus_sound {a=AMinus0 x y} =
>   rewrite optimize_0plus_sound {a=x} in
>   rewrite optimize_0plus_sound {a=y} in
>   Refl
> optimize_0plus_sound {a=AMult0 x y} =
>   rewrite optimize_0plus_sound {a=x} in
>   rewrite optimize_0plus_sound {a=y} in
>   Refl


== Coq Automation

\ \todo[inline]{Move the whole subsection to \idr{Pruviloj} chapter?}

The amount of repetition in this last proof is a little annoying. And if either
the language of arithmetic expressions or the optimization being proved sound
were significantly more complex, it would start to be a real problem.

So far, we've been doing all our proofs using just a small handful of Coq's
tactics and completely ignoring its powerful facilities for constructing parts
of proofs automatically. This section introduces some of these facilities, and
we will see more over the next several chapters. Getting used to them will take
some energy — Coq's automation is a power tool — but it will allow us to scale
up our efforts to more complex definitions and more interesting properties
without becoming overwhelmed by boring, repetitive, low-level details.


=== Tacticals

Tacticals is Coq's term for tactics that take other tactics as arguments —
"higher-order tactics," if you will.


==== The `try` Tactical

\ \todo[inline]{Exists in Pruviloj}

If `T` is a tactic, then `try T` is a tactic that is just like `T` except that,
if `T` fails, `try T` successfully does nothing at all (instead of failing).

```coq
Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try Refl. (* this just does Refl *) Qed.

Theorem silly2 : forall (P : Type), P -> P.
Proof.
  intros P HP.
  try Refl. (* just Refl would have failed *)
  apply HP. (* we can still finish the proof in some other way *)
Qed.
```

There is no real reason to use `try` in completely manual proofs like these, but
it is very useful for doing automated proofs in conjunction with the `;`
tactical, which we show next.


==== The `;` Tactical (Simple Form)

\ \todo[inline]{Approximated by \idr{andThen} in Pruviloj}

In its most common form, the `;` tactical takes two tactics as arguments. The
compound tactic `T;T'` first performs `T` and then performs `T'` on each subgoal
generated by `T`.

For example, consider the following trivial lemma:

```coq
Lemma foo : forall n, lte 0 n = True.
Proof.
  intros.
  destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. Refl.
    - (* n=Sn' *) simpl. Refl.
Qed.
```

We can simplify this proof using the `;` tactical:

```coq
Lemma foo' : forall n, lte 0 n = True.
Proof.
  intros.
  (* destruct the current goal *)
  destruct n;
  (* then simpl each resulting subgoal *)
  simpl;
  (* and do Refl on each resulting subgoal *)
  Refl.
Qed.
```

Using `try` and `;` together, we can get rid of the repetition in the proof that
was bothering us a little while ago.

\ \todo[inline]{Mention
\href{http://docs.idris-lang.org/en/latest/reference/misc.html\#alternatives}{Alternatives} ?}

```coq
Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; Refl).
    (* ... but the remaining cases -- ANum and APlus --
       are different: *)
  - (* ANum *) Refl.
  - (* APlus *)
    destruct a1;
      (* Again, most cases follow directly by the IH: *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; Refl).
    (* The interesting case, on which the try...
       does nothing, is when e1 = ANum n. In this
       case, we have to destruct n (to see whether
       the optimization applies) and rewrite with the
       induction hypothesis. *)
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; Refl. Qed.
```

Coq experts often use this "`...; try...`" idiom after a tactic like `induction`
to take care of many similar cases all at once. Naturally, this practice has an
analog in informal proofs. For example, here is an informal proof of the
optimization theorem that matches the structure of the formal one:

_Theorem_: For all arithmetic expressions `a`,
```
       aeval (optimize_0plus a) = aeval a.
```
_Proof_: By induction on `a`. Most cases follow directly from the `IH`. The
remaining cases are as follows:

  - Suppose `a = ANum n` for some `n`. We must show
```
       aeval (optimize_0plus (ANum n)) = aeval (ANum n).
```
    This is immediate from the definition of `optimize_0plus`.

  - Suppose `a = APlus a1 a2` for some `a1` and `a2`. We must show
```
       aeval (optimize_0plus (APlus a1 a2)) = aeval (APlus a1 a2).
```

    Consider the possible forms of `a1`. For most of them, `optimize_0plus`
    simply calls itself recursively for the subexpressions and rebuilds a new
    expression of the same form as `a1`; in these cases, the result follows
    directly from the `IH`. The interesting case is when `a1 = ANum n` for some
    `n`. If `n = ANum 0`, then
```
       optimize_0plus (APlus a1 a2) = optimize_0plus a2
```
    and the `IH` for `a2` is exactly what we need. On the other hand, if `n = S
    n'` for some `n'`, then again `optimize_0plus` simply calls itself
    recursively, and the result follows from the `IH`. $\square$

However, this proof can still be improved: the first case (for `a = ANum n`) is
very trivial — even more trivial than the cases that we said simply followed
from the `IH` — yet we have chosen to write it out in full. It would be better
and clearer to drop it and just say, at the top, "Most cases are either
immediate or direct from the `IH`. The only interesting case is the one for
`APlus...`" We can make the same improvement in our formal proof too. Here's how
it looks:

```coq
Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; Refl);
    (* ... or are immediate by definition *)
    try Refl.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; Refl).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; Refl. Qed.
```

==== The `;` Tactical (General Form)

The ; tactical also has a more general form than the simple `T;T'` we've seen
above. If `T, T1, ..., Tn` are tactics, then

```coq
      T; [T1 | T2 | ... | Tn]
```

is a tactic that first performs `T` and then performs `T1` on the first subgoal
generated by `T`, performs `T2` on the second subgoal, etc.

So `T;T'` is just special notation for the case when all of the `Ti`'s are the
same tactic; i.e.,` T;T`' is shorthand for:

```coq
      T; [T' | T' | ... | T']
```

==== The `repeat` Tactical

\ \todo[inline]{Approximated by \idr{repeatUntilFail} in Pruviloj}

The `repeat` tactical takes another tactic and keeps applying this tactic until
it fails. Here is an example showing that `10` is in a long list using `repeat`.

```coq
Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; Refl); right).
Qed.
```

The tactic `repeat T` never fails: if the tactic `T` doesn't apply to the
original goal, then repeat still succeeds without changing the original goal
(i.e., it repeats zero times).

```coq
Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; Refl).
  repeat (right; try (left; Refl)).
Qed.
```

The tactic `repeat T` also does not have any upper bound on the number of times
it applies `T`. If `T` is a tactic that always succeeds, then `repeat T` will
loop forever (e.g., `repeat simpl` loops forever, since `simpl` always
succeeds). While evaluation in Coq's term language, Gallina, is guaranteed to
terminate, tactic evaluation is not! This does not affect Coq's logical
consistency, however, since the job of `repeat` and other tactics is to guide
Coq in constructing proofs; if the construction process diverges, this simply
means that we have failed to construct a proof, not that we have constructed a
wrong one.


==== Exercise: 3 stars (optimize_0plus_b)

Since the \idr{optimize_0plus} transformation doesn't change the value of
\idr{AExp}s, we should be able to apply it to all the \idr{AExp}s that appear in
a \idr{BExp} without changing the \idr{BExp}'s value. Write a function which
performs that transformation on \idr{BExp}s, and prove it is sound. Use the
tacticals we've just seen to make the proof as elegant as possible.

> optimize_0plus_b : (b : BExp0) -> BExp0
> optimize_0plus_b b = ?optimize_0plus_b_rhs

> optimize_0plus_b_sound : beval0 (optimize_0plus_b b) = beval0 b
> optimize_0plus_b_sound = ?optimize_0plus_b_sound_rhs

$\square$


==== Exercise: 4 stars, optional (optimizer)

_Design exercise_: The optimization implemented by our \idr{optimize_0plus}
function is only one of many possible optimizations on arithmetic and boolean
expressions. Write a more sophisticated optimizer and prove it correct. (You
will probably find it easiest to start small — add just a single, simple
optimization and prove it correct — and build up to something more interesting
incrementially.)

> --FILL IN HERE

$\square$


=== Defining New Tactic Notations

Coq also provides several ways of "programming" tactic scripts.

  - The `Tactic Notation` idiom illustrated below gives a handy way to define
    "shorthand tactics" that bundle several tactics into a single command.

  - For more sophisticated programming, Coq offers a built-in programming
    language called `Ltac` with primitives that can examine and modify the proof
    state. The details are a bit too complicated to get into here (and it is
    generally agreed that `Ltac` is not the most beautiful part of Coq's
    design!), but they can be found in the reference manual and other books on
    Coq, and there are many examples of `Ltac` definitions in the Coq standard
    library that you can use as examples.

  - There is also an OCaml API, which can be used to build tactics that access
    Coq's internal structures at a lower level, but this is seldom worth the
    trouble for ordinary Coq users.

The `Tactic Notation` mechanism is the easiest to come to grips with, and it
offers plenty of power for many purposes. Here's an example.

```coq
Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.
```

This defines a new tactical called `simpl_and_try` that takes one tactic `c` as
an argument and is defined to be equivalent to the tactic `simpl; try c`. Now
writing "`simpl_and_try Refl.`" in a proof will be the same as writing "`simpl;
try Refl.`"


=== The `omega` Tactic

\ \todo[inline]{Related to https://github.com/forestbelton/cooper}

The `omega` tactic implements a decision procedure for a subset of first-order
logic called _Presburger arithmetic_. It is based on the Omega algorithm
invented in 1991 by William Pugh [Pugh 1991].

If the goal is a universally quantified formula made out of

  - numeric constants, addition (`+` and `S`), subtraction (`-` and `pred`), and
    multiplication by constants (this is what makes it Presburger arithmetic),

  - equality (`=` and `/=`) and inequality (`<=`), and

  - the logical connectives `/\`, `\/`, `Not`, and `->`,

then invoking `omega` will either solve the goal or tell you that it is actually
false.

```coq
Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.
```

=== A Few More Handy Tactics

Finally, here are some miscellaneous tactics that you may find convenient.

  - `clear H`: Delete hypothesis `H` from the context.

  - `subst x`: Find an assumption `x = e` or `e = x` in the context, replace `x`
     with `e` throughout the context and current goal, and clear the assumption.

  - `subst`: Substitute away all assumptions of the form `x = e` or `e = x`.

  - `rename... into...`: Change the name of a hypothesis in the proof context.
    For example, if the context includes a variable named `x`, then `rename x
    into y` will change all occurrences of `x` to `y`.

  - `assumption`: Try to find a hypothesis `H` in the context that exactly
    matches the goal; if one is found, behave like `apply H`.

  - `contradiction`: Try to find a hypothesis `H` in the current context that is
    logically equivalent to `Void`. If one is found, solve the goal.

  - `constructor`: Try to find a constructor `c` (from some `Inductive`
    definition in the current environment) that can be applied to solve the
    current goal. If one is found, behave like `apply c`.

We'll see examples below.


== Evaluation as a Relation

We have presented \idr{aeval} and \idr{beval} as functions. Another way to think
about evaluation — one that we will see is often more flexible — is as a
_relation_ between expressions and their values. This leads naturally to
\idr{data} definitions like the following one for arithmetic expressions...

```idris
data AEvalR : AExp0 -> Nat -> Type where
  E_ANum : (n: Nat) -> AEvalR (ANum n) n
  E_APlus : (e1, e2 : AExp0) -> (n1, n2 : Nat) ->
    AEvalR e1 n1 ->
    AEvalR e2 n2 ->
    AEvalR (APlus e1 e2) (n1 + n2)
  E_AMinus : (e1, e2 : AExp0) -> (n1, n2 : Nat) ->
    AEvalR e1 n1 ->
    AEvalR e2 n2 ->
    AEvalR (AMinus0 e1 e2) (n1 `minus` n2)
  E_AMult : (e1, e2: AExp0) -> (n1, n2 : Nat) ->
    AEvalR e1 n1 ->
    AEvalR e2 n2 ->
    AEvalR (AMult0 e1 e2) (n1 * n2)
```

\todo[inline]{Edit}

It will be convenient to have an infix notation for \idr{AEvalR}. We'll write
\idr{e \\ n} to mean that arithmetic expression \idr{e} evaluates to value
\idr{n}.

In fact, Idris provides a way to use this notation in the definition of
\idr{AevalR} itself. This reduces confusion by avoiding situations where we're
working on a proof involving statements in the form \idr{e \\ n} but we have to
refer back to a definition written using the form \idr{AEvalR e n}.

We do this by first "reserving" the notation, then giving the definition
together with a declaration of what the notation means.

> data (\\) : AExp0 -> (n : Nat) -> Type where
>   E_ANum : (ANum0 n) \\ n
>   E_APlus : e1 \\ n1 -> e2 \\ n2 -> n = n1 + n2 ->
>             (APlus0 e1 e2) \\ n

\todo[inline]{We don't use \idr{-} since it requires a proof of \idr{LTE n1 n2}}

>   E_AMinus : e1 \\ n1 -> e2 \\ n2 -> n = n1 `minus` n2 ->
>              (AMinus0 e1 e2) \\ n
>   E_AMult : e1 \\ n1 -> e2 \\ n2 -> n = n1 * n2 ->
>             (AMult0 e1 e2) \\ n

> AEvalR : AExp0 -> Nat -> Type
> AEvalR = (\\)


=== Inference Rule Notation

\ \todo[inline]{Add hyperlink}

In informal discussions, it is convenient to write the rules for \idr{AEvalR}
and similar relations in the more readable graphical form of inference rules,
where the premises above the line justify the conclusion below the line (we have
already seen them in the `IndProp` chapter).

For example, the constructor \idr{E_APlus}...

```idris
  E_APlus : (e1 \\ n1) -> (e2 \\ n2) -> (n = n1 + n2) ->
            (APlus0 e1 e2) \\ n
```

...would be written like this as an inference rule:

\[
  \begin{prooftree}
    \hypo{\idr{e1 \\ n1}}
    \hypo{\idr{e2 \\ n2}}
    \infer2[\idr{E_APlus}]{\idr{APlus e1 e2 \\ n1+n2}}
  \end{prooftree}
\]

Formally, there is nothing deep about inference rules: they are just
implications. You can read the rule name on the right as the name of the
constructor and read each of the linebreaks between the premises above the line
(as well as the line itself) as \idr{->}. All the variables mentioned in the
rule (\idr{e1}, \idr{n1}, etc.) are implicitly bound by universal quantifiers at
the beginning. (Such variables are often called _metavariables_ to distinguish
them from the variables of the language we are defining. At the moment, our
arithmetic expressions don't include variables, but we'll soon be adding them.)
The whole collection of rules is understood as being wrapped in an function
declaration. In informal prose, this is either elided or else indicated by
saying something like "Let \idr{AEvalR} be the smallest relation closed under
the following rules...".

For example, \idr{\\} is the smallest relation closed under these rules:

\[
  \begin{prooftree}
    \infer0[\idr{E_ANum}]{\idr{ANum n \\ n}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{e1 \\ n1}}
    \hypo{\idr{e2 \\ n2}}
    \infer2[\idr{E_APlus}]{\idr{APlus e1 e2 \\ n1+n2}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{e1 \\ n1}}
    \hypo{\idr{e2 \\ n2}}
    \infer2[\idr{E_AMinus}]{\idr{AMinus e1 e2 \\ n1-n2}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{e1 \\ n1}}
    \hypo{\idr{e2 \\ n2}}
    \infer2[\idr{E_AMult}]{\idr{AMult e1 e2 \\ n1*n2}}
  \end{prooftree}
\]


=== Equivalence of the Definitions

It is straightforward to prove that the relational and functional definitions of
evaluation agree:

> aeval_iff_aevalR : (a \\ n) <-> aeval0 a = n
> aeval_iff_aevalR = (to, fro)
> where
>   to : (a \\ n) -> aeval0 a = n
>   to E_ANum = Refl
>   to (E_APlus x y xy) =
>     rewrite xy in
>     rewrite to x in
>     rewrite to y in Refl
>   to (E_AMinus x y xy) =
>     rewrite xy in
>     rewrite to x in
>     rewrite to y in Refl
>   to (E_AMult x y xy) =
>     rewrite xy in
>     rewrite to x in
>     rewrite to y in Refl
>   fro : (aeval0 a = n) -> (a \\ n)
>   fro {a=ANum0 n} Refl = E_ANum
>   fro {a=APlus0 x y} prf =
>     E_APlus (fro Refl) (fro Refl) (sym prf)
>   fro {a=AMinus0 x y} prf =
>     E_AMinus (fro Refl) (fro Refl) (sym prf)
>   fro {a=AMult0 x y} prf =
>     E_AMult (fro Refl) (fro Refl) (sym prf)

We can make the proof quite a bit shorter by making more use of tacticals.

```coq
Theorem aeval_iff_aevalR' : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  - (* -> *)
    intros H; induction H; subst; Refl.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; Refl.
Qed.
```

==== Exercise: 3 stars (bevalR)

Write a relation \idr{BEvalR} in the same style as \idr{AEvalR}, and prove that
it is equivalent to \idr{beval0}.

> -- data BEvalR : BExp0 -> (b : Bool) -> Type where
>   -- FILL IN HERE
>
> -- beval_iff_bevalR : (BEvalR b bv) <-> beval0 b = bv

$\square$


=== Computational vs. Relational Definitions

For the definitions of evaluation for arithmetic and boolean expressions, the
choice of whether to use functional or relational definitions is mainly a matter
of taste: either way works.

However, there are circumstances where relational definitions of evaluation work
much better than functional ones.

For example, suppose that we wanted to extend the arithmetic operations by
considering also a division operation:

> namespace AEvalRDiv

>   data AExpD : Type where
>     ANumD : Nat -> AExpD
>     APlusD : AExpD -> AExpD -> AExpD
>     AMinusD : AExpD -> AExpD -> AExpD
>     AMultD : AExpD -> AExpD -> AExpD
>     ADivD : AExpD -> AExpD -> AExpD -- <--- new

Extending the definition of \idr{aeval} to handle this new operation would not
be straightforward (what should we return as the result of
\idr{ADiv (ANum 5) (ANum 0)}?). But extending \idr{AEvalR} is straightforward.

>   infix 5 \\\

>   data (\\\) : AExpD -> (n : Nat) -> Type where
>     E_ANumD : (ANumD n) \\\ n
>     E_APlusD : e1 \\\ n1 -> e2 \\\ n2 -> n = n1 + n2 ->
>       (APlusD e1 e2) \\\ n
>     E_AMinusD : e1 \\\ n1 -> e2 \\\ n2 -> n = n1 `minus` n2 ->
>       (AMinusD e1 e2) \\\ n
>     E_AMultD : e1 \\\ n1 -> e2 \\\ n2 -> n = n1 * n2 ->
>       (AMultD e1 e2) \\\ n
>     E_ADivD : e1 \\\ n1 -> e2 \\\ n2 -> n2 `GT` 0 -> n1 = n2*n3 ->
>       (ADivD e1 e2) \\\ n3

>   AEvalRD : AExpD -> Nat -> Type
>   AEvalRD = (\\\)

Suppose, instead, that we want to extend the arithmetic operations by a
nondeterministic number generator \idr{any} that, when evaluated, may yield any
number. (Note that this is not the same as making a _probabilistic_ choice among
all possible numbers — we're not specifying any particular distribution of
results, but just saying what results are _possible_.)

> namespace AEvalRAny

>   data AExpA : Type where
>     AAnyA : AExpA -- <--- new
>     ANumA : Nat -> AExpA
>     APlusA : AExpA -> AExpA -> AExpA
>     AMinusA : AExpA -> AExpA -> AExpA
>     AMultA : AExpA -> AExpA -> AExpA

Again, extending \idr{aeval} would be tricky, since now evaluation is _not_ a
deterministic function from expressions to numbers, but extending \idr{AEvalR}
is no problem:

>   infix 5 \\\

>   data (\\\) : AExpA -> (n : Nat) -> Type where
>     E_AnyA : AAnyA \\\ n
>     E_ANumA : (ANumA n) \\\ n
>     E_APlusA : e1 \\\ n1 -> e2 \\\ n2 -> n = n1 + n2 ->
>       (APlusA e1 e2) \\\ n
>     E_AMinusA : e1 \\\ n1 -> e2 \\\ n2 -> n = n1 `minus` n2 ->
>       (AMinusA e1 e2) \\\ n
>     E_AMultA : e1 \\\ n1 -> e2 \\\ n2 -> n = n1 * n2 ->
>       (AMultA e1 e2) \\\ n

>   AEvalRA : AExpA -> Nat -> Type
>   AEvalRA = (\\\)

At this point you maybe wondering: which style should I use by default? The
examples above show that relational definitions are fundamentally more powerful
than functional ones. For situations like these, where the thing being defined
is not easy to express as a function, or indeed where it is _not_ a function,
there is no choice. But what about when both styles are workable?

\ \todo[inline]{Edit}

One point in favor of relational definitions is that some people feel they are
more elegant and easier to understand. Another is that Idris automatically
generates nice inversion and induction principles from function definitions.

On the other hand, functional definitions can often be more convenient:

  - Functions are by definition deterministic and defined on all arguments; for
    a relation we have to show these properties explicitly if we need them.

  - With functions we can also take advantage of Idris's computation mechanism
    to simplify expressions during proofs.

Furthermore, functions can be directly "extracted" to executable code in C
or JavaScript.

Ultimately, the choice often comes down to either the specifics of a particular
situation or simply a question of taste. Indeed, in large Idris developments it
is common to see a definition given in _both_ functional and relational styles,
plus a lemma stating that the two coincide, allowing further proofs to switch
from one point of view to the other at will.


== Expressions With Variables

Let's turn our attention back to defining Imp. The next thing we need to do is
to enrich our arithmetic and Boolean expressions with variables. To keep things
simple, we'll assume that all variables are global and that they only hold
numbers.


=== States

Since we'll want to look variables up to find out their current values, we'll
reuse the type \idr{Id} from the `Maps` chapter for the type of variables in
Imp.

A _machine state_ (or just _state_) represents the current values of _all_
variables at some point in the execution of a program.

For simplicity, we assume that the state is defined for _all_ variables, even
though any given program is only going to mention a finite number of them. The
state captures all of the information stored in memory. For Imp programs,
because each variable stores a natural number, we can represent the state as a
mapping from identifiers to \idr{Nat}. For more complex programming languages,
the state might have more structure.

> State : Type
> State = TotalMap Nat

> empty_state : State
> empty_state = t_empty 0


=== Syntax

We can add variables to the arithmetic expressions we had before by simply
adding one more constructor:

> data AExp : Type where
>   ANum : Nat -> AExp
>   AId : Id -> AExp -- <----- NEW
>   APlus : AExp -> AExp -> AExp
>   AMinus : AExp -> AExp -> AExp
>   AMult : AExp -> AExp -> AExp

Defining a few variable names as notational shorthands will make examples easier
to read:

> W : Id
> W = MkId "W"
> X : Id
> X = MkId "X"
> Y : Id
> Y = MkId "Y"
> Z : Id
> Z = MkId "Z"

\todo[inline]{Edit}

(This convention for naming program variables (\idr{X}, \idr{Y}, \idr{Z})
clashes a bit with our earlier use of uppercase letters for types. Since we're
not using polymorphism heavily in the chapters devoped to Imp, this overloading
should not cause confusion.)

The definition of \idr{BExp}s is unchanged (except for using the new
\idr{AExp}s):

> data BExp : Type where
>   BTrue : BExp
>   BFalse : BExp
>   BEq : AExp -> AExp -> BExp
>   BLe : AExp -> AExp -> BExp
>   BNot : BExp -> BExp
>   BAnd : BExp -> BExp -> BExp


=== Evaluation

The arith and boolean evaluators are extended to handle variables in the obvious
way, taking a state as an extra argument:

> aeval : (st : State) -> (a : AExp) -> Nat
> aeval _ (ANum n) = n
> aeval st (AId i) = st i
> aeval st (APlus a1 a2) = (aeval st a1) + (aeval st a2)
> aeval st (AMinus a1 a2) = (aeval st a1) `minus` (aeval st a2)
> aeval st (AMult a1 a2) = (aeval st a1) * (aeval st a2)
>
> beval : (st : State) -> (b : BExp) -> Bool
> beval _ BTrue = True
> beval _ BFalse = False
> beval st (BEq a1 a2) = (aeval st a1) == (aeval st a2)
> beval st (BLe a1 a2) = lte (aeval st a1) (aeval st a2)
> beval st (BNot b1) = not (beval st b1)
> beval st (BAnd b1 b2) = (beval st b1) && (beval st b2)

> aexp1 : aeval (t_update X 5 Imp.empty_state)
>               (APlus (ANum 3) (AMult (AId X) (ANum 2)))
>         = 13
> aexp1 = Refl

> bexp1 : beval (t_update X 5 Imp.empty_state)
>               (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
>         = True
> bexp1 = Refl


== Commands

Now we are ready define the syntax and behavior of Imp _commands_ (sometimes
called _statements_).


=== Syntax

Informally, commands \idr{c} are described by the following BNF grammar. (We
choose this slightly awkward concrete syntax for the sake of being able to
define Imp syntax using Idris's \idr{syntax} mechanism. In particular, we use
\idr{IFB} to avoid conflicting with the \idr{if} notation from the standard
library.)

```
     c ::= SKIP | x ::= a | c ;; c | IFB b THEN c ELSE c FI
         | WHILE b DO c END
```

For example, here's factorial in Imp:

```
     Z ::= X;;
     Y ::= 1;;
     WHILE not (Z = 0) DO
       Y ::= Y * Z;;
       Z ::= Z - 1
     END
```

When this command terminates, the variable \idr{Y} will contain the factorial of
the initial value of \idr{X}.

Here is the formal definition of the abstract syntax of commands:

> data Com : Type where
>   CSkip : Com
>   CAss : Id -> AExp -> Com
>   CSeq : Com -> Com -> Com
>   CIf : BExp -> Com -> Com -> Com
>   CWhile : BExp -> Com -> Com

As usual, we can use a few `Notation` declarations to make things more readable.
To avoid conflicts with Idris's built-in notations, we keep this light — in
particular, we don't introduce any notations for \idr{AExp}s and \idr{BExp}s to
avoid confusion with the numeric and boolean operators we've already defined.

\ \todo[inline]{Explain do-notation}

> infix 5 ::= 

> SKIP : Com
> SKIP = CSkip

> (::=) : Id -> AExp -> Com
> (::=) = CAss

> (>>=) : Com -> (() -> Com) -> Com
> (>>=) c f = CSeq c (f ())

> WHILE : BExp -> Com -> Com
> WHILE = CWhile

> syntax IFB [c1] THEN [c2] ELSE [c3] FI = CIf c1 c2 c3

For example, here is the factorial function again, written as a formal
definition to Idris:

> fact_in_idris : Com
> fact_in_idris = do
>  Z ::= AId X
>  Y ::= ANum 1
>  WHILE (BNot (BEq (AId Z) (ANum 0))) $ do
>    Y ::= AMult (AId Y) (AId Z)
>    Z ::= AMinus (AId Z) (ANum 1)


=== More Examples


==== Assignment:

> plus2 : Com
> plus2 =
>  X ::= APlus (AId X) (ANum 2)

> XtimesYinZ : Com
> XtimesYinZ =
>  Z ::= AMult (AId X) (AId Y)

> subtract_slowly_body : Com
> subtract_slowly_body = do
>   Z ::= AMinus (AId Z) (ANum 1)
>   X ::= AMinus (AId X) (ANum 1)


==== Loops

> subtract_slowly : Com
> subtract_slowly =
>  WHILE (BNot (BEq (AId X) (ANum 0))) $ do
>    subtract_slowly_body

> subtract_3_from_5_slowly : Com
> subtract_3_from_5_slowly = do
>   X ::= ANum 3
>   Z ::= ANum 5
>   subtract_slowly


==== An infinite loop:

> loop : Com
> loop = WHILE BTrue SKIP


== Evaluating Commands

Next we need to define what it means to evaluate an Imp command. The fact that
\idr{WHILE} loops don't necessarily terminate makes defining an evaluation
function tricky...


=== Evaluation as a Function (Failed Attempt)

Here's an attempt at defining an evaluation function for commands, omitting the
\idr{WHILE} case.

> ceval_fun_no_while : (st : State) -> (c : Com) -> State
> ceval_fun_no_while st CSkip = st
> ceval_fun_no_while st (CAss x a) = t_update x (aeval st a) st
> ceval_fun_no_while st (CSeq c1 c2) =
>   let st' = ceval_fun_no_while st c1
>   in ceval_fun_no_while st' c2
> ceval_fun_no_while st (CIf b c1 c2) =
>   if beval st b
>     then ceval_fun_no_while st c1
>     else ceval_fun_no_while st c2
> ceval_fun_no_while st (CWhile b c) = st   -- bogus

In a traditional functional programming language like OCaml or Haskell we could
add the \idr{WHILE} case as follows:

```idris
...
ceval_fun st (CWhile b c) =
  if (beval st b)
    then ceval_fun st (CSeq c $ CWhile b c)
    else st
```

Idris doesn't accept such a definition ("Imp.ceval_fun is possibly not total due
to recursive path Imp.ceval_fun --> Imp.ceval_fun --> Imp.ceval_fun") because
the function we want to define is not guaranteed to terminate. Indeed, it
_doesn't_ always terminate: for example, the full version of the \idr{ceval_fun}
function applied to the \idr{loop} program above would never terminate. Since
Idris is not just a functional programming language but also a consistent logic,
any potentially non-terminating function needs to be rejected. Here is an
(invalid!) program showing what would go wrong if Idris allowed non-terminating
recursive functions:

\ \todo[inline]{Edit, discuss \idr{partial}}

```idris
loop_false : (n : Nat) -> Void
loop_false n = loop_false n
```

That is, propositions like \idr{Void} would become provable (\idr{loop_false 0}
would be a proof of \idr{Void}), which would be a disaster for Idris's logical
consistency.

Thus, because it doesn't terminate on all inputs, \idr{ceval_fun} cannot be
written in Idris — at least not without additional tricks and workarounds (see
chapter `ImpCEvalFun` if you're curious about what those might be).


=== Evaluation as a Relation

Here's a better way: define \idr{CEval} as a _relation_ rather than a _function_
— i.e., define it with \idr{data}, as we did for \idr{AEvalR} above.

This is an important change. Besides freeing us from awkward workarounds, it
gives us a lot more flexibility in the definition. For example, if we add
nondeterministic features like \idr{any} to the language, we want the definition
of evaluation to be nondeterministic — i.e., not only will it not be total, it
will not even be a function!

We'll use the notation \idr{c / st \\ st'} for the \idr{CEval} relation:
\idr{c / st \\ st'} means that executing program \idr{c} in a starting state
\idr{st} results in an ending state \idr{st'}. This can be pronounced "\idr{c}
takes state \idr{st} to \idr{st'}".


==== Operational Semantics

Here is an informal definition of evaluation, presented as inference rules for
readability:

\[
  \begin{prooftree}
    \infer0[\idr{E_Skip}]{\idr{SKIP / st \\ st}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{aeval st a1 = n}}
    \infer1[\idr{E_Ass}]{\idr{x := a1 / st \\ (t_update st x n)}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{c1 / st \\ st'}}
    \hypo{\idr{c2 / st' \\ st''}}
    \infer2[\idr{E_Seq}]{\idr{c1;;c2 / st \\ st''}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{beval st b1 = True}}
    \hypo{\idr{c1 / st \\ st'}}
    \infer2[\idr{E_IfTrue}]{\idr{IF b1 THEN c1 ELSE c2 FI / st \\ st'}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{beval st b1 = False}}
    \hypo{\idr{c2 / st \\ st'}}
    \infer2[\idr{E_IfFalse}]{\idr{IF b1 THEN c1 ELSE c2 FI / st \\ st'}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{beval st b = False}}
    \infer1[\idr{E_WhileEnd}]{\idr{WHILE b DO c END / st \\ st}}
  \end{prooftree}
\]

\[
  \begin{prooftree}
    \hypo{\idr{beval st b = True}}
    \hypo{\idr{c / st \\ st'}}
    \hypo{\idr{WHILE b DO c END / st' \\ st''}}
    \infer3[\idr{E_WhileLoop}]{\idr{WHILE b DO c END / st \\ st''}}
  \end{prooftree}
\]

Here is the formal definition. Make sure you understand how it corresponds to
the inference rules.

> data CEval : Com -> State -> State -> Type where
>   E_Skip : CEval CSkip st st
>   E_Ass : aeval st a1 = n -> CEval (CAss x a1) st (t_update x n st)
>   E_Seq : CEval c1 st st' -> CEval c2 st' st'' ->
>     CEval (CSeq c1 c2) st st''
>   E_IfTrue : beval st b = True -> CEval c1 st st' ->
>     CEval (CIf b c1 c2) st st'
>   E_IfFalse : beval st b = False -> CEval c2 st st' ->
>     CEval (CIf b c1 c2) st st'
>   E_WhileEnd : beval st b = False ->
>     CEval (CWhile b c) st st
>   E_WhileLoop : beval st b = True ->
>     CEval c st st' -> CEval (CWhile b c) st' st'' ->
>     CEval (CWhile b c) st st''

> syntax [c1] "/" [st] "\\\\" [st'] = CEval c1 st st'

The cost of defining evaluation as a relation instead of a function is that we
now need to construct _proofs_ that some program evaluates to some result state,
rather than just letting Idris's computation mechanism do it for us.

 test : Com
 test = do 
   X ::= ANum 2
   IFB BLe (AId X) (ANum 1)
     THEN (Y ::= ANum 3)
     ELSE (Z ::= ANum 4)
   FI


> ceval_example1 : (do
>   X ::= ANum 2
>   IFB BLe (AId X) (ANum 1)
>     THEN (Y ::= ANum 3)
>     ELSE (Z ::= ANum 4)
>   FI) 
>   / Imp.empty_state 
>  \\ (t_update Z 4 $ t_update X 2 $ Imp.empty_state)
> ceval_example1 =
>   E_Seq
>     (E_Ass Refl)
>     (E_IfFalse Refl
>                (E_Ass Refl))


==== Exercise: 2 stars (ceval_example2)

> ceval_example2 : (do 
>    X ::= ANum 0
>    Y ::= ANum 1
>    Z ::= ANum 2)
>    / Imp.empty_state
>   \\ (t_update Z 2 $ t_update Y 1 $ t_update X 0 $ Imp.empty_state)
> ceval_example2 = ?ceval_example2_rhs

$\square$


==== Exercise: 3 stars, advanced (pup_to_n)

Write an Imp program that sums the numbers from \idr{1} to \idr{X} (inclusive:
\idr{1 + 2 + ... + X}) in the variable \idr{Y}. Prove that this program executes
as intended for \idr{X = 2} (this is trickier than you might expect).

> pup_to_n : Com
> pup_to_n = ?pup_to_n_rhs

> pup_to_2_ceval :
>   Imp.pup_to_n / (t_update X 2 Imp.empty_state) \\
>    (t_update X 0 $
>     t_update Y 3 $
>     t_update X 1 $
>     t_update Y 2 $
>     t_update Y 0 $
>     t_update X 2 $ 
>     Imp.empty_state)
> pup_to_2_ceval = ?pup_to_2_ceval_rhs

$\square$


=== Determinism of Evaluation

Changing from a computational to a relational definition of evaluation is a good
move because it frees us from the artificial requirement that evaluation should
be a total function. But it also raises a question: Is the second definition of
evaluation really a partial function? Or is it possible that, beginning from the
same state \idr{st}, we could evaluate some command \idr{c} in different ways to
reach two different output states \idr{st'} and \idr{st''}?

In fact, this cannot happen: \idr{CEval} _is_ a partial function:

> ceval_deterministic : (c / st \\ st1) -> (c / st \\ st2) -> st1 = st2
> ceval_deterministic E_Skip E_Skip = Refl
> ceval_deterministic (E_Ass aev1) (E_Ass aev2) =
>   rewrite sym aev1 in
>   rewrite sym aev2 in Refl
> ceval_deterministic {st2} (E_Seq cev11 cev12)
>                           (E_Seq {c2} cev21 cev22) =
>   let ih = ceval_deterministic cev11 cev21
>       cev22' = replace (sym ih) cev22 {P=\x=>CEval c2 x st2}
>   in ceval_deterministic cev12 cev22'
> ceval_deterministic (E_IfTrue _ cev1) (E_IfTrue _ cev2) =
>   ceval_deterministic cev1 cev2
> ceval_deterministic (E_IfTrue prf1 _) (E_IfFalse prf2 _) =
>   absurd $ replace prf1 prf2 {P=\x=>x=False}
> ceval_deterministic (E_IfFalse prf1 _) (E_IfTrue prf2 _) =
>   absurd $ replace prf2 prf1 {P=\x=>x=False}
> ceval_deterministic (E_IfFalse _ cev1) (E_IfFalse _ cev2) =
>   ceval_deterministic cev1 cev2
> ceval_deterministic (E_WhileEnd _) (E_WhileEnd _) = Refl
> ceval_deterministic (E_WhileEnd prf1) (E_WhileLoop prf2 _ _) =
>   absurd $ replace prf2 prf1 {P=\x=>x=False}
> ceval_deterministic (E_WhileLoop prf1 _ _) (E_WhileEnd prf2) =
>   absurd $ replace prf1 prf2 {P=\x=>x=False}
> ceval_deterministic {st2} (E_WhileLoop _ cev11 cev12)
>                           (E_WhileLoop {b} {c} _ cev21 cev22) =
>   let ih = ceval_deterministic cev11 cev21
>       cev22' = replace (sym ih) cev22 {P=\x=>CEval (CWhile b c) x st2}
>   in ceval_deterministic cev12 cev22'


== Reasoning About Imp Programs

We'll get deeper into systematic techniques for reasoning about Imp programs in
the following chapters, but we can do quite a bit just working with the bare
definitions. This section explores some examples.

> plus2_spec : st X = n -> (Imp.plus2 / st \\ st') -> st' X = n + 2

\todo[inline]{Edit}

Inverting `Heval` essentially forces Idris to expand one step of the \idr{CEval}
computation — in this case revealing that \idr{st'} must be st extended with the
new value of \idr{X}, since \idr{plus2} is an assignment

> plus2_spec Refl (E_Ass Refl) = Refl


==== Exercise: 3 stars, recommendedM (XtimesYinZ_spec)

State and prove a specification of \idr{XtimesYinZ}.

> -- FILL IN HERE

$\square$


==== Exercise: 3 stars, recommended (loop_never_stops)

> loop_never_stops : Not (Imp.loop / st \\ st')
> loop_never_stops contra = ?loop_never_stops_rhs

\todo[inline]{Edit the hint}

```coq
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef
           eqn:Heqloopdef.
```

Proceed by induction on the assumed derivation showing that loopdef terminates.
Most of the cases are immediately contradictory (and so can be solved in one
step with inversion).

  (* FILL IN HERE *) Admitted.

$\square$


==== Exercise: 3 stars (no_whilesR)

Consider the following function:

> no_whiles : (c : Com) -> Bool
> no_whiles CSkip = True
> no_whiles (CAss _ _) = True
> no_whiles (CSeq c1 c2) = (no_whiles c1) && (no_whiles c2)
> no_whiles (CIf _ ct cf) = (no_whiles ct) && (no_whiles cf)
> no_whiles (CWhile _ _) = False

This predicate yields \idr{True} just on programs that have no while loops.
Using \idr{data}, write a property \idr{No_whilesR} such that \idr{No_whilesR c}
is provable exactly when \idr{c} is a program with no while loops. Then prove
its equivalence with \idr{no_whiles}.

> data No_whilesR : Com -> Type where
>   Remove_Me_No_whilesR : No_whilesR CSkip

> no_whiles_eqv : (no_whiles c = True) <-> (No_whilesR c)
> no_whiles_eqv = ?no_whiles_eqv_rhs

$\square$


==== Exercise: 4 starsM (no_whiles_terminating)

Imp programs that don't involve while loops always terminate. State and prove a
theorem \idr{no_whiles_terminating} that says this. Use either \idr{no_whiles}
or \idr{No_whilesR}, as you prefer.

> -- FILL IN HERE

$\square$


== Additional Exercises


==== Exercise: 3 stars (stack_compiler)

HP Calculators, programming languages like Forth and Postscript and abstract
machines like the Java Virtual Machine all evaluate arithmetic expressions using
a stack. For instance, the expression

```
      (2*3)+(3*(4-2))
```

would be entered as

```
      2 3 * 3 4 2 - * +
```

and evaluated like this (where we show the program being evaluated on the right
and the contents of the stack on the left):

```
      [ ]           |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |
```

The task of this exercise is to write a small compiler that translates
\idr{AExp}s into stack machine instructions.

The instruction set for our stack language will consist of the following
instructions:

  - \idr{SPush n}: Push the number \idr{n} on the stack.

  - \idr{SLoad x}: Load the identifier \idr{x} from the store and push it on the
    stack

  - \idr{SPlus}: Pop the two top numbers from the stack, add them, and push the
    result onto the stack.

  - \idr{SMinus}: Similar, but subtract.

  - \idr{SMult}: Similar, but multiply.

> data SInstr : Type where
>   SPush : Nat -> SInstr
>   SLoad : Id -> SInstr
>   SPlus : SInstr
>   SMinus : SInstr
>   SMult : SInstr

Write a function to evaluate programs in the stack language. It should take as
input a state, a stack represented as a list of numbers (top stack item is the
head of the list), and a program represented as a list of instructions, and it
should return the stack after executing the program. Test your function on the
examples below.

Note that the specification leaves unspecified what to do when encountering an
\idr{SPlus}, \idr{SMinus}, or \idr{SMult} instruction if the stack contains less
than two elements. In a sense, it is immaterial what we do, since our compiler
will never emit such a malformed program.

> s_execute : (st : State) -> (stack : List Nat) -> (prog : List SInstr) ->
>             List Nat
> s_execute st stack prog = ?s_execute_rhs

> s_execute1 : s_execute Imp.empty_state [] [SPush 5, SPush 3, SPush 1, SMinus]
>              = [2,5]
> s_execute1 = ?s_execute1_rhs

> s_execute2 : s_execute (t_update X 3 Imp.empty_state) [3,4]
>                        [SPush 4, SLoad X, SMult, SPlus]
>              = [15,4]
> s_execute2 = ?s_execute2_rhs

Next, write a function that compiles an \idr{AExp} into a stack machine program.
The effect of running the program should be the same as pushing the value of the
expression on the stack.

> s_compile : (e : AExp) -> List SInstr
> s_compile e = ?s_compile_rhs

After you've defined \idr{s_compile}, prove the following to test that it works.

> s_compile1 : s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
>              = [SLoad X, SPush 2, SLoad Y, SMult, SMinus]
> s_compile1 = ?s_compile1_rhs

$\square$


==== Exercise: 4 stars, advanced (stack_compiler_correct)

Now we'll prove the correctness of the compiler implemented in the previous
exercise. Remember that the specification left unspecified what to do when
encountering an \idr{SPlus}, \idr{SMinus}, or \idr{SMult} instruction if the
stack contains less than two elements. (In order to make your correctness proof
easier you might find it helpful to go back and change your implementation!)

Prove the following theorem. You will need to start by stating a more general
lemma to get a usable induction hypothesis; the main theorem will then be a
simple corollary of this lemma.

\ \todo[inline]{Tip: make parameters explicit in general lemma, or Idris will 
get lost}

> s_compile_correct : (st : State) -> (e : AExp) -> s_execute st [] (s_compile e) = [aeval st e]
> s_compile_correct st e = ?s_compile_correct_rhs

$\square$


==== Exercise: 3 stars, optional (short_circuit)

\ \todo[inline]{This already happens since Idris's \idr{&&} short-circuits}

Most modern programming languages use a "short-circuit" evaluation rule for
boolean \idr{and}: to evaluate \idr{BAnd b1 b2}, first evaluate \idr{b1}. If it
evaluates to \idr{False}, then the entire \idr{BAnd} expression evaluates to
\idr{False} immediately, without evaluating \idr{b2}. Otherwise, \idr{b2} is
evaluated to determine the result of the \idr{BAnd} expression.

Write an alternate version of \idr{beval} that performs short-circuit
evaluation of \idr{BAnd} in this manner, and prove that it is equivalent to
\idr{beval}.

> -- FILL IN HERE

$\square$


==== Exercise: 4 stars, advanced (break_imp)

Imperative languages like C and Java often include a \idr{break} or similar
statement for interrupting the execution of loops. In this exercise we consider
how to add \idr{break} to Imp. First, we need to enrich the language of commands
with an additional case.

> namespace ComBreak

>   data ComB : Type where
>     CSkipB : ComB
>     CBreakB : ComB  -- <-- new
>     CAssB : Id -> AExp -> ComB
>     CSeqB : ComB -> ComB -> ComB
>     CIfB : BExp -> ComB -> ComB -> ComB
>     CWhileB : BExp -> ComB -> ComB

>   infix 5 ::=

>   SKIP : ComB
>   SKIP = CSkipB

>   BREAK : ComB
>   BREAK = CBreakB

>   (::=) : Id -> AExp -> ComB
>   (::=) = CAssB

>   (>>=) : ComB -> (() -> ComB) -> ComB
>   (>>=) c f = CSeqB c (f ())

>   WHILE : BExp -> ComB -> ComB
>   WHILE = CWhileB

>   syntax IFB [c1] THEN [c2] ELSE [c3] FI = CIfB c1 c2 c3

Next, we need to define the behavior of \idr{BREAK}. Informally, whenever
\idr{BREAK} is executed in a sequence of commands, it stops the execution of
that sequence and signals that the innermost enclosing loop should terminate.
(If there aren't any enclosing loops, then the whole program simply terminates.)
The final state should be the same as the one in which the \idr{BREAK} statement
was executed.

One important point is what to do when there are multiple loops enclosing a
given \idr{BREAK}. In those cases, \idr{BREAK} should only terminate the
_innermost_ loop. Thus, after executing the following...

```
       X ::= 0;;
       Y ::= 1;;
       WHILE not (0 == Y) DO
         WHILE TRUE DO
           BREAK
         END;;
         X ::= 1;;
         Y ::= Y - 1
       END
```

... the value of \idr{X} should be \idr{1}, and not \idr{0}.

One way of expressing this behavior is to add another parameter to the
evaluation relation that specifies whether evaluation of a command executes a
\idr{BREAK} statement:

>   data Result : Type where
>     SContinue : Result
>     SBreak : Result

Intuitively, \idr{c // st \\ s / st'} means that, if \idr{c} is started in state
\idr{st}, then it terminates in state \idr{st'} and either signals that the
innermost surrounding loop (or the whole program) should exit immediately
(\idr{s = SBreak}) or that execution should continue normally
(\idr{s = SContinue}).

The definition of the "\idr{c // st \\ s / st'}" relation is very similar to the
one we gave above for the regular evaluation relation (\idr{c / st \\ st'}) —
we just need to handle the termination signals appropriately:

  - If the command is \idr{SKIP}, then the state doesn't change and execution of
    any enclosing loop can continue normally.

  - If the command is \idr{BREAK}, the state stays unchanged but we signal a
    \idr{SBreak}.

  - If the command is an assignment, then we update the binding for that
    variable in the state accordingly and signal that execution can continue
    normally.

  - If the command is of the form \idr{IFB b THEN c1 ELSE c2 FI}, then the state
    is updated as in the original semantics of Imp, except that we also
    propagate the signal from the execution of whichever branch was taken.

  - If the command is a sequence \idr{c1 ;; c2}, we first execute \idr{c1}. If
    this yields a \idr{SBreak}, we skip the execution of \idr{c2} and propagate
    the \idr{SBreak} signal to the surrounding context; the resulting state is
    the same as the one obtained by executing \idr{c1} alone. Otherwise, we
    execute \idr{c2} on the state obtained after executing \idr{c1}, and
    propagate the signal generated there.

  - Finally, for a loop of the form \idr{WHILE b DO c END}, the semantics is
    almost the same as before. The only difference is that, when \idr{b}
    evaluates to \idr{True}, we execute \idr{c} and check the signal that it
    raises. If that signal is \idr{SContinue}, then the execution proceeds as in
    the original semantics. Otherwise, we stop the execution of the loop, and
    the resulting state is the same as the one resulting from the execution of
    the current iteration. In either case, since \idr{BREAK} only terminates the
    innermost loop, \idr{WHILE} signals \idr{SContinue}.

Based on the above description, complete the definition of the \idr{CEvalB}
relation.

>   data CEvalB : ComB -> State -> Result -> State -> Type where
>     E_SkipB : CEvalB CSkipB st SContinue st
>     -- FILL IN HERE

>   syntax [c1] "//" [st] "\\\\" [s] "/" [st'] = CEvalB c1 st s st'

Now prove the following properties of your definition of \idr{CEvalB}:

>   break_ignore : ((do BREAK; c) // st \\ s / st') -> st = st'
>   break_ignore x = ?break_ignore_rhs


>   while_continue : ((WHILE b c) // st \\ s / st') -> s = SContinue
>   while_continue x = ?while_continue_rhs

>   while_stops_on_break : beval st b = True ->
>                          (c // st \\ SBreak / st') ->
>                          ((WHILE b c) // st \\ SContinue / st')
>   while_stops_on_break prf x = ?while_stops_on_break_rhs

$\square$


==== Exercise: 3 stars, advanced, optional (while_break_true)

>   while_break_true : ((WHILE b c) // st \\ SContinue / st') ->
>                      beval st' b = True ->
>                      (st'' ** c // st'' \\ SBreak / st')
>   while_break_true x prf = ?while_break_true_rhs

$\square$


==== Exercise: 4 stars, advanced, optional (cevalB_deterministic)

These will come in handy in the following exercise:

>   Uninhabited (SBreak = SContinue) where
>     uninhabited Refl impossible
>
>   Uninhabited (SContinue = SBreak) where
>     uninhabited Refl impossible

>   cevalB_deterministic : (c // st \\ s1 / st1) ->
>                          (c // st \\ s2 / st2) ->
>                          (st1 = st2, s1 = s2)
>   cevalB_deterministic x y = ?cevalB_deterministic_rhs

$\square$


==== Exercise: 4 stars, optional (add_for_loop)

Add C-style \idr{for} loops to the language of commands, update the \idr{CEval}
definition to define the semantics of \idr{for} loops, and add cases for
\idr{for} loops as needed so that all the proofs in this file are accepted by
Idris.

A \idr{for} loop should be parameterized by (a) a statement executed initially,
(b) a test that is run on each iteration of the loop to determine whether the
loop should continue, (c) a statement executed at the end of each loop
iteration, and (d) a statement that makes up the body of the loop. (You don't
need to worry about making up a concrete notation for \idr{for} loops, but feel
free to play with this too if you like.)

> -- FILL IN HERE

$\square$
