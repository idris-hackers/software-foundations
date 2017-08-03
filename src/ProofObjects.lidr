= ProofObjects : The Curry-Howard Correspondence

> module ProofObjects

\say{\textit{Algorithms are the computational content of proofs.}}
-- Robert Harper

We have seen that Idris has mechanisms both for _programming_, using inductive
data types like \idr{Nat} or \idr{List} and functions over these types, and for
_proving_ properties of these programs, using inductive propositions (like
\idr{Ev}), implication, universal quantification, and the like. So far, we have
mostly treated these mechanisms as if they were quite separate, and for many
purposes this is a good way to think. But we have also seen hints that Idris's
programming and proving facilities are closely related. For example, the keyword
\idr{data} is used to declare both data types and propositions, and \idr{->} is
used both to describe the type of functions on data and logical implication.
This is not just a syntactic accident! In fact, programs and proofs in Idris are
almost the same thing. In this chapter we will study how this works.

We have already seen the fundamental idea: provability in Idris is represented
by concrete _evidence_. When we construct the proof of a basic proposition, we
are actually building a tree of evidence, which can be thought of as a data
structure.

If the proposition is an implication like \idr{A -> B}, then its proof will be
an evidence _transformer_: a recipe for converting evidence for \idr{A} into
evidence for \idr{B}. So at a fundamental level, proofs are simply programs that
manipulate evidence.

Question: If evidence is data, what are propositions themselves?

Answer: They are types!

Look again at the formal definition of the \idr{Ev} property.

> data Ev : Nat -> Type where
>   Ev_0 : Ev Z
>   Ev_SS : {n : Nat} -> Ev n -> Ev (S (S n))

Suppose we introduce an alternative pronunciation of "\idr{:}". Instead of "has
type," we can say "is a proof of." For example, the second line in the
definition of \idr{Ev} declares that \idr{Ev_0 : Ev 0}. Instead of "\idr{Ev_0}
has type \idr{Ev }0," we can say that "\idr{Ev_0} is a proof of \idr{Ev 0}."

This pun between types and propositions — between \idr{:} as "has type" and
\idr{:} as "is a proof of" or "is evidence for" — is called the Curry-Howard
correspondence. It proposes a deep connection between the world of logic and the
world of computation:

                 propositions  ~  types
                 proofs        ~  data values

\todo[inline]{Add link}

See [Wadler 2015] for a brief history and an up-to-date exposition.

Many useful insights follow from this connection. To begin with, it gives us a
natural interpretation of the type of the \idr{Ev_SS} constructor:

```idris
λΠ> :t Ev_SS
Ev_SS : Ev n -> Ev (S (S n))
```

This can be read "\idr{Ev_SS} is a constructor that takes two arguments — a
number \idr{n} and evidence for the proposition \idr{Ev n} — and yields evidence
for the proposition \idr{Ev (S (S n))}."

Now let's look again at a previous proof involving \idr{Ev}.

> ev_4 : Ev 4
> ev_4 = Ev_SS {n=2} $ Ev_SS {n=0} Ev_0

As with ordinary data values and functions, we can use the \idr{:printdef}
command to see the proof object that results from this proof script.

```idris
λΠ> :printdef ev_4
ev_4 : Ev 4
ev_4 = Ev_SS (Ev_SS Ev_0)
```

As a matter of fact, we can also write down this proof object directly, without
the need for a separate proof script:

\todo[inline]{Doesn't work in Idris REPL}

```coq
Check (ev_SS 2 (ev_SS 0 ev_0)).
(* ===> ev 4 *)
```

The expression \idr{Ev_SS {n=2} $ Ev_SS {n=0} Ev_0} can be thought of as
instantiating the parameterized constructor \idr{Ev_SS} with the specific
arguments \idr{2} and \idr{0} plus the corresponding proof objects for its
premises \idr{Ev 2} and \idr{Ev 0}. Alternatively, we can think of \idr{Ev_SS}
as a primitive "evidence constructor" that, when applied to a particular number,
wants to be further applied to evidence that that number is even; its type,

```idris
      {n : Nat} -> Ev n -> Ev (S (S n))
```

expresses this functionality, in the same way that the polymorphic type
\idr{{x : Type} -> List x} expresses the fact that the constructor \idr{Nil} can
be thought of as a function from types to empty lists with elements of that
type.

\todo[inline]{Edit or remove}

We saw in the `Logic` chapter that we can use function application syntax to
instantiate universally quantified variables in lemmas, as well as to supply
evidence for assumptions that these lemmas impose. For instance:

```coq
Theorem ev_4': ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.
```

We can now see that this feature is a trivial consequence of the status the
Idris grants to proofs and propositions: Lemmas and hypotheses can be combined
in expressions (i.e., proof objects) according to the same basic rules used for
programs in the language.


== Proof Scripts

\ \todo[inline]{Rewrite, keep explanation about holes? Seems a bit late for
that}

The _proof objects_ we've been discussing lie at the core of how Idris operates.
When Idris is following a proof script, what is happening internally is that it
is gradually constructing a proof object — a term whose type is the proposition
being proved. The expression on the right hand side of \idr{=} tell it how to
build up a term of the required type. To see this process in action, let's use
the `Show Proof` command to display the current state of the proof tree at
various points in the following tactic proof.

```coq
Theorem ev_4'' : ev 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.
```

At any given moment, Idris has constructed a term with a "hole" (indicated by
`?Goal` here, and so on), and it knows what type of evidence is needed to fill
this hole.

Each hole corresponds to a subgoal, and the proof is finished when there are no
more subgoals. At this point, the evidence we've built stored in the global
context under the name given in the type definition.

Tactic proofs are useful and convenient, but they are not essential: in
principle, we can always construct the required evidence by hand, as shown
above. Then we can use `Definition` (rather than `Theorem`) to give a global
name directly to a piece of evidence.

```coq
Definition ev_4''' : ev 4 :=
  ev_SS 2 (ev_SS 0 ev_0).
```

All these different ways of building the proof lead to exactly the same evidence
being saved in the global environment.

```coq
Print ev_4.
(* ===> ev_4    =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'.
(* ===> ev_4'   =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4''.
(* ===> ev_4''  =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
Print ev_4'''.
(* ===> ev_4''' =   ev_SS 2 (ev_SS 0 ev_0) : ev 4 *)
```

==== Exercise: 1 star (eight_is_even)

\ \todo[inline]{Remove?}

Give a tactic proof and a proof object showing that \idr{Ev 8}.

> ev_8 : Ev 8
> ev_8 = ?ev_8_rhs

$\square$


==== Quantifiers, Implications, Functions

\ \todo[inline]{Edit the section}

In Idris's computational universe (where data structures and programs live),
there are two sorts of values with arrows in their types: _constructors_
introduced by \idr{data} definitions, and _functions_.

Similarly, in Idris's logical universe (where we carry out proofs), there are
two ways of giving evidence for an implication: constructors introduced by
\idr{data}-defined propositions, and... functions!

For example, consider this statement:

> ev_plus4 : Ev n -> Ev (4 + n)
> ev_plus4 x = Ev_SS $ Ev_SS x

What is the proof object corresponding to ev_plus4?

We're looking for an expression whose type is \idr{{n: Nat} -> Ev n -> Ev (4 +
n)} — that is, a function that takes two arguments (one number and a piece of
evidence) and returns a piece of evidence! Here it is:

```coq
Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun (n : Nat) => fun (H : ev n) =>
    ev_SS (S (S n)) (ev_SS n H).
```

Recall that `fun n => blah` means "the function that, given \idr{n}, yields
\idr{blah}," and that Idris treats \idr{4 + n} and \idr{S (S (S (S n)))} as
synonyms. Another equivalent way to write this definition is:

```coq
Definition ev_plus4'' (n : Nat) (H : ev n) : ev (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4''.
(* ===> ev_plus4'' : forall n : Nat, ev n -> ev (4 + n) *)
```

When we view the proposition being proved by \idr{ev_plus4} as a function type,
one aspect of it may seem a little unusual. The second argument's type, \idr{Ev
n}, mentions the _value_ of the first argument, \idr{n}. While such _dependent
types_ are not found in conventional programming languages, they can be useful
in programming too, as the recent flurry of activity in the functional
programming community demonstrates.

\todo[inline]{Reword?}

Notice that both implication (\idr{->}) and quantification (\idr{(x : t) -> f
x}) correspond to functions on evidence. In fact, they are really the same
thing: \idr{->} is just a shorthand for a degenerate use of quantification where
there is no dependency, i.e., no need to give a name to the type on the
left-hand side of the arrow.

For example, consider this proposition:

> ev_plus2 : Type
> ev_plus2 = (n : Nat) -> (e : Ev n) -> Ev (n + 2)

A proof term inhabiting this proposition would be a function with two arguments:
a number \idr{n} and some evidence \idr{e} that \idr{n} is even. But the name
\idr{e} for this evidence is not used in the rest of the statement of
\idr{ev_plus2}, so it's a bit silly to bother making up a name for it. We could
write it like this instead:

> ev_plus2' : Type
> ev_plus2' = (n : Nat) -> Ev n -> Ev (n + 2)

In general, "\idr{p -> q}" is just syntactic sugar for "\idr{(_ : p) -> q}".


== Programming with Tactics

\ \todo[inline]{Edit and move to an appendix about ElabReflection/Pruviloj?}

If we can build proofs by giving explicit terms rather than executing tactic
scripts, you may be wondering whether we can build _programs_ using _tactics_ rather
than explicit terms. Naturally, the answer is yes!

```coq
Definition add1 : Nat -> Nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print add1.
(* ==>
    add1 = fun n : Nat => S n
         : Nat -> Nat
*)

Compute add1 2.
(* ==> 3 : Nat *)
```

Notice that we terminate the `Definition` with a `.` rather than with `:=`
followed by a term. This tells Idris to enter _proof scripting mode_ to build an
object of type \idr{Nat -> Nat}. Also, we terminate the proof with `Defined`
rather than `Qed`; this makes the definition _transparent_ so that it can be
used in computation like a normally-defined function. (`Qed`-defined objects are
opaque during computation.)

This feature is mainly useful for writing functions with dependent types, which
we won't explore much further in this book. But it does illustrate the
uniformity and orthogonality of the basic ideas in Idris.


== Logical Connectives as Inductive Types

Inductive definitions are powerful enough to express most of the connectives and
quantifiers we have seen so far. Indeed, only universal quantification (and thus
implication) is built into Idris; all the others are defined inductively. We'll
see these definitions in this section.


=== Conjunction

\ \todo[inline]{Edit/remove most of this}

To prove that \idr{(p,q)} holds, we must present evidence for both \idr{p} and
\idr{q}. Thus, it makes sense to define a proof object for \idr{(p,q)} as
consisting of a pair of two proofs: one for \idr{p} and another one for \idr{q}.
This leads to the following definition.

> data And : (p, q : Type) -> Type where
>   Conj : p -> q -> And p q

Notice the similarity with the definition of the \idr{Prod} type, given in chapter
`Poly`; the only difference is that \idr{Prod} takes Type arguments, whereas and takes
Prop arguments.

```idris
data Prod : (x, y : Type) -> Type where
  PPair : x -> y -> Prod x y
```

This should clarify why pattern matching can be used on a conjunctive
hypothesis. Case analysis allows us to consider all possible ways in which
\idr{(p,q)} was proved — here just one (the \idr{Conj} constructor). Similarly,
the `split` tactic actually works for any inductively defined proposition with
only one constructor. In particular, it works for \idr{And}:

\todo[inline]{Copied `<->` for now}

> iff : {p,q : Type} -> Type
> iff {p} {q} = (p -> q, q -> p)
>
> syntax [p] "<->" [q] = iff {p} {q}


> and_comm : (And p q) <-> (And q p)
> and_comm = (\(Conj x y) => Conj y x,
>             \(Conj y x) => Conj x y)


This shows why the inductive definition of and can be manipulated by tactics as
we've been doing. We can also use it to build proofs directly, using
pattern-matching. For instance:

```coq
Definition and_comm'_aux P Q (H : P /\ Q) :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).
```


==== Exercise: 2 stars, optional (conj_fact)

Construct a proof object demonstrating the following proposition.

> conj_fact : And p q -> And q r -> And p r
> conj_fact pq qr = ?conj_fact_rhs

$\square$


=== Disjunction

The inductive definition of disjunction uses two constructors, one for each side
of the disjunct:

> data Or : (p, q : Type) -> Type where
>   IntroL : p -> Or p q
>   IntroR : q -> Or p q

This declaration explains the behavior of pattern matching on a disjunctive
hypothesis, since the generated subgoals match the shape of the \idr{IntroL} and
\idr{IntroR} constructors.

Once again, we can also directly write proof objects for theorems involving
\idr{Or}, without resorting to tactics.


==== Exercise: 2 stars, optional (or_comm)

\ \todo[inline]{Edit}

Try to write down an explicit proof object for \idr{or_comm} (without using
`Print` to peek at the ones we already defined!).

> or_comm : Or p q -> Or q p
> or_comm pq = ?or_comm_rhs

$\square$


=== Existential Quantification

To give evidence for an existential quantifier, we package a witness \idr{x}
together with a proof that \idr{x} satisfies the property \idr{p}:

> data Ex : (p : a -> Type) -> Type where
>   ExIntro : (x : a) -> p x -> Ex p

This may benefit from a little unpacking. The core definition is for a type
former \idr{Ex} that can be used to build propositions of the form \idr{Ex p},
where \idr{p} itself is a function from witness values in the type \idr{a} to
propositions. The \idr{ExIntro} constructor then offers a way of constructing
evidence for \idr{Ex p}, given a witness \idr{x} and a proof of \idr{p x}.

The more familiar form \idr{(x ** p x)} desugars to an expression involving
\idr{Ex}:

\todo[inline]{Edit}

```coq
Check ex (fun n => ev n).
(* ===> exists n : Nat, ev n
        : Prop *)
```

Here's how to define an explicit proof object involving \idr{Ex}:

> some_nat_is_even : Ex (\n => Ev n)
> some_nat_is_even = ExIntro 4 (Ev_SS $ Ev_SS Ev_0)


==== Exercise: 2 stars, optional (ex_ev_Sn)

Complete the definition of the following proof object:

> ex_ev_Sn : Ex (\n => Ev (S n))
> ex_ev_Sn = ?ex_ev_Sn_rhs

$\square$


\subsection{\idr{Unit} and \idr{Void}}

The inductive definition of the \idr{Unit} proposition is simple:

```idris
data Unit : Type where
  () : Unit
```

It has one constructor (so every proof of \idr{Unit} is the same, so being given
a proof of\idr{Unit} is not informative.)

\idr{Void} is equally simple — indeed, so simple it may look syntactically wrong
at first glance!

\todo[inline]{Edit, this actually is wrong, stdlib uses \idr{runElab} to define
it}

```idris
data Void : Type where
```

That is, \idr{Void} is an inductive type with _no_ constructors — i.e., no way
to build evidence for it.


== Equality

\ \todo[inline]{Edit, it actually is built in}

Even Idris's equality relation is not built in. It has the following inductive
definition. (Actually, the definition in the standard library is a small variant
of this, which gives an induction principle that is slightly easier to use.)

> data PropEq : {t : Type} -> t -> t -> Type where
>   EqRefl : PropEq x x

> syntax [x] "='" [y] = PropEq x y

The way to think about this definition is that, given a set \idr{t}, it defines
a _family_ of propositions "\idr{x} is equal to \idr{y}," indexed by pairs of
values (\idr{x} and \idr{y}) from \idr{t}. There is just one way of constructing
evidence for each member of this family: applying the constructor \idr{EqRefl}
to a type \idr{t} and a value \idr{x : t} yields evidence that \idr{x} is equal
to \idr{x}.


==== Exercise: 2 stars (leibniz_equality)

The inductive definition of equality corresponds to _Leibniz equality_: what we
mean when we say "\idr{x} and \idr{y} are equal" is that every property \idr{p}
that is true of \idr{x} is also true of \idr{y}.

> leibniz_equality : (x =' y) -> ((p : t -> Type) -> p x -> p y)
> leibniz_equality eq p px = ?leibniz_equality_rhs

$\square$

\todo[inline]{Edit}

We can use \idr{EqRefl} to construct evidence that, for example, \idr{2 = 2}.
Can we also use it to construct evidence that \idr{1 + 1 = 2}? Yes, we can.
Indeed, it is the very same piece of evidence! The reason is that Idris treats
as "the same" any two terms that are _convertible_ according to a simple set of
computation rules. These rules, which are similar to those used by `Compute`,
include evaluation of function application, inlining of definitions, and
simplification of `match`es.

> four : (2 + 2) =' (1 + 3)
> four = EqRefl

The \idr{Refl} that we have used to prove equalities up to now is essentially
just an application of an equality constructor.

\todo[inline]{Edit}

In tactic-based proofs of equality, the conversion rules are normally hidden in
uses of `simpl` (either explicit or implicit in other tactics such as
`reflexivity`). But you can see them directly at work in the following explicit
proof objects:

```coq
Definition four' : 2 + 2 = 1 + 3 :=
  eq_refl 4.
```

> singleton : ([]++[x]) =' (x::[])
> singleton = EqRefl

> quiz6 : Ex (\x => (x + 3) =' 4)
> quiz6 = ExIntro 1 EqRefl


=== Inversion, Again

\ \todo[inline]{Edit/remove}

We've seen `inversion` used with both equality hypotheses and hypotheses about
inductively defined propositions. Now that we've seen that these are actually
the same thing, we're in a position to take a closer look at how `inversion`
behaves.

In general, the `inversion` tactic...

  - takes a hypothesis `H` whose type `P` is inductively defined, and

  - for each constructor `C` in `P`'s definition,

    - generates a new subgoal in which we assume `H` was built with `C`,

    - adds the arguments (premises) of `C` to the context of the subgoal as
      extra hypotheses,

    - matches the conclusion (result type) of `C` against the current goal and
      calculates a set of equalities that must hold in order for `C` to be
      applicable,

    - adds these equalities to the context (and, for convenience, rewrites them
      in the goal), and

    - if the equalities are not satisfiable (e.g., they involve things like
      \idr{S n = Z}), immediately solves the subgoal.

_Example_: If we invert a hypothesis built with \idr{Or}, there are two
constructors, so two subgoals get generated. The conclusion (result type) of the
constructor (\idr{Or p q}) doesn't place any restrictions on the form of \idr{p}
or \idr{q}, so we don't get any extra equalities in the context of the subgoal.

_Example_: If we invert a hypothesis built with \idr{And}, there is only one
constructor, so only one subgoal gets generated. Again, the conclusion (result
type) of the constructor (\idr{And p q}) doesn't place any restrictions on the
form of \idr{p} or \idr{q}, so we don't get any extra equalities in the context
of the subgoal. The constructor does have two arguments, though, and these can
be seen in the context in the subgoal.

_Example_: If we invert a hypothesis built with \idr{PropEq}, there is again
only one constructor, so only one subgoal gets generated. Now, though, the form
of the \idr{EqRefl} constructor does give us some extra information: it tells us
that the two arguments to \idr{PropEq} must be the same! The `inversion` tactic
adds this fact to the context.
