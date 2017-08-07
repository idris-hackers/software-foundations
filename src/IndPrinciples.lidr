= IndPrinciples : Induction Principles

> module IndPrinciples

> %access public export
> %default total

With the Curry-Howard correspondence and its realization in Idris in mind, we
can now take a deeper look at induction principles.


== Basics

\ \todo[inline]{Edit, this is probably also made redundant by pattern matching}

Every time we declare a new \idr{data} type, Idris automatically generates an
_induction principle_ for this type. This induction principle is a theorem like
any other: If \idr{t} is defined inductively, the corresponding induction
principle is called \idr{t_ind}. Here is the one for natural numbers:

> nat_ind : {P : Nat -> Type} -> P Z -> ((n : Nat) -> P n -> P (S n)) ->
>           ((n : Nat) -> P n)
> nat_ind pz _ Z = pz
> nat_ind pz f (S k) = f k (nat_ind pz f k)

\todo[inline]{Mention it's no coincidence it's similar to fold}

The `induction` tactic is a straightforward wrapper that, at its core, simply
performs `apply t_ind`. To see this more clearly, let's experiment with directly
using `apply nat_ind`, instead of the `induction` tactic, to carry out some
proofs. Here, for example, is an alternate proof of a theorem that we saw in the
`Induction` chapter.

> mult_0_r' : (n : Nat) -> n * Z = Z
> mult_0_r' = nat_ind {P=\x => x*Z = Z}
>   Refl             -- n = Z
>   (\k => id)       -- n = S k

This proof is basically the same as the earlier one, but a few minor differences
are worth noting.

First, in the induction step of the proof (the "\idr{S}" case), we have to do a
little bookkeeping manually (the `intros`) that `induction` does automatically.

Second, we do not introduce \idr{n} into the context before applying
\idr{nat_ind} — the conclusion of \idr{nat_ind} is a quantified formula, and
`apply` needs this conclusion to exactly match the shape of the goal state,
including the quantifier. By contrast, the `induction` tactic works either with
a variable in the context or a quantified variable in the goal.

These conveniences make `induction` nicer to use in practice than applying
induction principles like \idr{nat_ind} directly. But it is important to realize
that, modulo these bits of bookkeeping, applying \idr{nat_ind} is what we are
really doing.


==== Exercise: 2 stars, optional (plus_one_r')

Complete this proof without using the `induction` tactic.

> plus_one_r' : (n : Nat) -> n + 1 = S n
> plus_one_r' n = ?plus_one_r__rhs


$\square$

Idris generates induction principles for every datatype defined with \idr{data},
including those that aren't recursive. Although of course we don't need
induction to prove properties of non-recursive datatypes, the idea of an
induction principle still makes sense for them: it gives a way to prove that a
property holds for all values of the type.

These generated principles follow a similar pattern. If we define a type \idr{t}
with constructors \idr{c1} ... \idr{cn}, Idris generates a theorem with this
shape:

```idris
t_ind : {P : t -> Type},
          ... case for c1 ... ->
          ... case for c2 ... -> ...
          ... case for cn ... ->
        (n : t) -> P n
```

The specific shape of each case depends on the arguments to the corresponding
constructor. Before trying to write down a general rule, let's look at some more
examples. First, an example where the constructors take no arguments:

> data YesNo = Yes' | No'

> yesno_ind : {P : YesNo -> Type} -> P Yes' -> P No' ->
>             ((y : YesNo) -> P y)
> yesno_ind px _ Yes' = px
> yesno_ind _ py No'  = py


==== Exercise: 1 star, optional (rgb)

Write out the induction principle that Idris will generate for the following
datatype. Write down your answer on paper or type it into a comment, and then
compare it with what Idris prints.

> data RGB = Red | Green | Blue

> rgb_ind : ?rgb_ind

$\square$

Here's another example, this time with one of the constructors taking some
arguments.

> data NatList : Type where
>   NNil : NatList
>   NCons : Nat -> NatList -> NatList

> natlist_ind : {P : NatList -> Type} -> P NNil ->
>               ((n : Nat) -> (l : NatList) -> P l -> P (NCons n l)) ->
>               ((l : NatList) -> P l)
> natlist_ind pn _ NNil = pn
> natlist_ind pn f (NCons k x) = f k x (natlist_ind pn f x)


==== Exercise: 1 star, optional (natlist1)

Suppose we had written the above definition a little differently:

> data NatList1 : Type where
>   NNil1 : NatList1
>   NCons1 : NatList1 -> Nat -> NatList1

Now what will the induction principle look like? $\square$

From these examples, we can extract this general rule:

  - The type declaration gives several constructors; each corresponds to one
    clause of the induction principle.

  - Each constructor \idr{c} takes argument types \idr{a1} ... \idr{an}.

  - Each \idr{ai} can be either \idr{t} (the datatype we are defining) or some
    other type \idr{s}.

  - The corresponding case of the induction principle says:

    - "For all values \idr{x1}...\idr{xn} of types \idr{a1}...\idr{an}, if
      \idr{P} holds for each of the inductive arguments (each \idr{xi} of type
      \idr{t}), then \idr{P} holds for \idr{c x1 ... xn}".


==== Exercise: 1 star, optional (byntree_ind)

Write out the induction principle that Idris will generate for the following
datatype. (Again, write down your answer on paper or type it into a comment, and
then compare it with what Idris prints.)

> data Byntree : Type where
>  Bempty : Byntree
>  Bleaf : YesNo -> Byntree
>  Nbranch : YesNo -> Byntree -> Byntree -> Byntree

$\square$


==== Exercise: 1 star, optional (ex_set)

Here is an induction principle for an inductively defined set.

```idris
ExSet_ind : {P : ExSet -> Type} -> ((b : Bool) -> P (Con1 b)) ->
           ((n : Nat) -> (e : ExSet) -> P e -> P (Con2 n e)) ->
           ((e : ExSet) -> P e)
```

Give an \idr{data} definition of \idr{ExSet}:

> -- data ExSet : Type where
> -- FILL IN HERE

$\square$


== Polymorphism

Next, what about polymorphic datatypes?

The inductive definition of polymorphic lists

```idris
data List : (x : Type) -> Type where
  Nil : List x
  Cons : x -> List x -> List x
```

is very similar to that of \idr{NatList}. The main difference is that, here, the
whole definition is _parameterized_ on a set \idr{x}: that is, we are defining a
family of inductive types \idr{List x}, one for each \idr{x}. (Note that,
wherever \idr{List} appears in the body of the declaration, it is always applied
to the parameter \idr{x}.) The induction principle is likewise parameterized on
\idr{x}:

> list_ind : {x : Type} -> {P : List x -> Type} -> P [] ->
>            ((a : x) -> (l : List x) -> P l -> P (a :: l)) ->
>            ((l : List x) -> P l)
> list_ind pn _ [] = pn
> list_ind pn f (h::t) = f h t (list_ind pn f t)

Note that the whole induction principle is parameterized on \idr{x}. That is,
\idr{list_ind} can be thought of as a polymorphic function that, when applied to
a type \idr{x}, gives us back an induction principle specialized to the type
\idr{List x}.


==== Exercise: 1 star, optional (tree)

Write out the induction principle that Idris will generate for the following
datatype. Compare your answer with what Idris prints.

> data Tree : (x : Type) -> Type where
>   Leaf : x -> Tree x
>   Node : Tree x -> Tree x -> Tree x

> tree_ind : ?tree_ind

$\square$


==== Exercise: 1 star, optional (mytype)

Find an inductive definition that gives rise to the following induction
principle:

```idris
mytype_ind : {x : Type} -> {P : MyType x -> Type} ->
             ((a : x) -> P (Constr1 a)) ->
             ((n : Nat) -> P (Constr2 n)) ->
             ((m : MyType x) -> P m -> (n : Nat) -> P (Constr3 m n)) ->
             ((m : MyType x) -> P m)
```

$\square$


==== Exercise: 1 star, optional (foo)

Find an inductive definition that gives rise to the following induction
principle:

```idris
foo_ind : {x, y : Type} -> {P : Foo x y -> Type} ->
       ((a : x) -> P (Bar a)) ->
       ((b : y) -> P (Baz b)) ->
       ((f1 : Nat -> Foo x y) -> ((n : Nat) -> P (f1 n)) -> P (Quux f1)) ->
       ((f2 : Foo x y) -> P f2)
```

$\square$


==== Exercise: 1 star, optional (foo')

Consider the following inductive definition:

> data Foo' : (x : Type) -> Type where
>   C1 : List x -> Foo' x -> Foo' x
>   C2 : Foo' x

What induction principle will Idris generate for \idr{Foo'}? Fill in the blanks,
then check your answer with Idris.)

```idris
foo'_ind : {x : Type} -> {P : Foo' x -> Type} ->
           ((l : List x) -> (f : Foo' x) -> ?hole1 -> ?hole2) ->
           ?hole3 ->
           (f : Foo' x -> ?hole4)
```

$\square$


== Induction Hypotheses

Where does the phrase "induction hypothesis" fit into this story?

The induction principle for numbers

```idris
nat_ind : {P : Nat -> Type} -> P Z -> ((n : Nat) -> P n -> P (S n)) ->
          ((n : Nat) -> P n)
``

is a generic statement that holds for all propositions \idr{P} (or rather,
strictly speaking, for all families of propositions \idr{P} indexed by a number
\idr{n}). Each time we use this principle, we are choosing \idr{P} to be a
particular expression of type \idr{Nat -> Type}.

We can make proofs by induction more explicit by giving this expression a name.
For example, instead of stating the theorem \idr{mult_0_r} as
"\idr{(n : Nat) -> n * 0 = 0}," we can write it as "\idr{(n : Nat) -> P_m0r n}",
where \idr{P_m0r} is defined as...

> P_m0r : (n : Nat) -> Type
> P_m0r n = n * Z = Z

... or equivalently:

> P_m0r' : Nat -> Type
> P_m0r' = \n => n * Z = Z

Now it is easier to see where \idr{P_m0r} appears in the proof.

> mult_0_r'' : (n: Nat) -> P_m0r n
> mult_0_r'' = nat_ind {P=P_m0r}
>   Refl             -- n = Z
>   (\n => id)       -- n = S k

This extra naming step isn't something that we do in normal proofs, but it is
useful to do it explicitly for an example or two, because it allows us to see
exactly what the induction hypothesis is. If we prove \idr{(n : Nat) -> P_m0r n}
by induction on \idr{n} (using either `induction` or `apply nat_ind`), we see
that the first subgoal requires us to prove \idr{P_m0r 0} ("\idr{P} holds for
zero"), while the second subgoal requires us to prove
\idr{(n' : Nat) -> P_m0r n' -> P_m0r (S n')} (that is "\idr{P} holds of
\idr{S n'} if it holds of \idr{n'}" or, more elegantly, "\idr{P} is preserved by
\idr{S}"). The _induction hypothesis_ is the premise of this latter implication
— the assumption that \idr{P} holds of \idr{n'}, which we are allowed to use in
proving that \idr{P} holds for \idr{S n'}.


== More on the `induction` Tactic

The `induction` tactic actually does even more low-level bookkeeping for us than
we discussed above.

Recall the informal statement of the induction principle for natural numbers:

  - If \idr{P n} is some proposition involving a natural number \idr{n}, and we
    want to show that \idr{P} holds for all numbers \idr{n}, we can reason like
    this:

    - show that \idr{P Z} holds

    - show that, if \idr{P n'} holds, then so does \idr{P (S n')}

    - conclude that \idr{P n} holds for all \idr{n}.

So, when we begin a proof with `intros n` and then `induction n`, we are first
telling Idris to consider a _particular_ `n` (by introducing it into the
context) and then telling it to prove something about _all_ numbers (by using
induction).

What Idris actually does in this situation, internally, is to "re-generalize"
the variable we perform induction on. For example, in our original proof that
\idr{plus} is associative...

```coq
Theorem plus_assoc' : forall n m p : Nat,
  n + (m + p) = (n + m) + p.
Proof.
  (* ...we first introduce all 3 variables into the context,
     which amounts to saying "Consider an arbitrary n, m, and
     p..." *)
  intros n m p.
  (* ...We now use the induction tactic to prove P n (that
     is, n + (m + p) = (n + m) + p) for _all_ n,
     and hence also for the particular n that is in the context
     at the moment. *)
  induction n as [| n'].
  - (* n = O *) Refl.
  - (* n = S n' *)
    (* In the second subgoal generated by induction -- the
       "inductive step" -- we must prove that P n' implies
       P (S n') for all n'.  The induction tactic
       automatically introduces n' and P n' into the context
       for us, leaving just P (S n') as the goal. *)
    simpl. rewrite -> IHn'. Refl. Qed.
```

It also works to apply `induction` to a variable that is quantified in the goal.

```coq
Theorem plus_comm' : forall n m : Nat,
  n + m = m + n.
Proof.
  induction n as [| n'].
  - (* n = O *) intros m. rewrite <- plus_n_O. Refl.
  - (* n = S n' *) intros m. simpl. rewrite -> IHn'.
    rewrite <- plus_n_Sm. Refl. Qed.
```

Note that `induction n` leaves `m` still bound in the goal — i.e., what we are
proving inductively is a statement beginning with `forall m`.

If we do `induction` on a variable that is quantified in the goal _after_ some
other quantifiers, the `induction` tactic will automatically introduce the
variables bound by these quantifiers into the context.

```coq
Theorem plus_comm'' : forall n m : Nat,
  n + m = m + n.
Proof.
  (* Let's do induction on m this time, instead of n... *)
  induction m as [| m'].
  - (* m = O *) simpl. rewrite <- plus_n_O. Refl.
  - (* m = S m' *) simpl. rewrite <- IHm'.
    rewrite <- plus_n_Sm. Refl. Qed.
```


==== Exercise: 1 star, optional (plus_explicit_prop)

Rewrite both \idr{plus_assoc'} and \idr{plus_comm'} and their proofs in the same
style as \idr{mult_0_r''} above — that is, for each theorem, give an explicit
definition of the proposition being proved by induction, and state the theorem
and proof in terms of this defined proposition.

> -- FILL IN HERE

$\square$


== Induction Principles in \idr{Type}

Earlier, we looked in detail at the induction principles that Idris generates
for inductively defined _sets_. The induction principles for inductively defined
_propositions_ like \idr{Ev} are a tiny bit more complicated. As with all
induction principles, we want to use the induction principle on \idr{Ev} to
prove things by inductively considering the possible shapes that something in
\idr{Ev} can have. Intuitively speaking, however, what we want to prove are not
statements about evidence but statements about _numbers_: accordingly, we want
an induction principle that lets us prove properties of numbers by induction on
evidence.

For example, from what we've said so far, you might expect the inductive
definition of \idr{Ev}...

\todo[inline]{Redefine for now}

> data Ev : Nat -> Type where
>   Ev_0 : Ev Z
>   Ev_SS : Ev n -> Ev (S (S n))

...to give rise to an induction principle that looks like this...

> ev_ind_max : {P : {n : Nat} -> Ev n -> Type} ->
>        P {n=Z} Ev_0 ->
>        ((m : Nat) -> (e : Ev m) -> P {n=m} e -> P {n=S (S m)} (Ev_SS e)) ->
>        ((n : Nat) -> (e : Ev n) -> P {n} e)

... because:

  - Since \idr{Ev} is indexed by a number \idr{n} (every \idr{Ev} object \idr{e}
    is a piece of evidence that some particular number \idr{n} is even), the
    proposition \idr{P} is parameterized by both \idr{n} and \idr{e} — that is,
    the induction principle can be used to prove assertions involving both an
    even number and the evidence that it is even.

  - Since there are two ways of giving evidence of evenness (\idr{Ev} has two
    constructors), applying the induction principle generates two subgoals:

    - We must prove that \idr{P} holds for \idr{Z} and \idr{Ev_0}.

    - We must prove that, whenever \idr{n} is an even number and \idr{e} is an
      evidence of its evenness, if \idr{P} holds of \idr{n} and \idr{e}, then it
      also holds of \idr{S (S n)} and \idr{Ev_SS {n=S (S n)} e}.

  - If these subgoals can be proved, then the induction principle tells us that
    \idr{P} is true for all even numbers \idr{n} and evidence \idr{e} of their
    evenness.

This is more flexibility than we normally need or want: it is giving us a way to
prove logical assertions where the assertion involves properties of some piece
of _evidence_ of evenness, while all we really care about is proving properties
of _numbers_ that are even — we are interested in assertions about numbers, not
about evidence. It would therefore be more convenient to have an induction
principle for proving propositions \idr{P} that are parameterized just by
\idr{n} and whose conclusion establishes \idr{P} for all even numbers \idr{n}:

```idris
       {P : Nat -> Type} ->
       ... ->
       (n : Nat) ->
       Ev n -> P n
```

For this reason, Idris actually generates the following simplified induction
principle for \idr{Ev}:

> ev_ind : {P : Nat -> Type} -> P Z ->
>         ((n : Nat) -> Ev n -> P n -> P (S (S n))) ->
>         ((n : Nat) -> Ev n -> P n)
> ev_ind pz _ Z Ev_0 = pz
> ev_ind pz f (S (S k)) (Ev_SS ev) = f k ev (ev_ind pz f k ev)

In particular, Idris has dropped the evidence term \idr{e} as a parameter of the
the proposition \idr{P}.

In English, \idr{ev_ind} says:

  - Suppose, \idr{P} is a property of natural numbers (that is, \idr{P n} is a
    \idr{Type} for every \idr{n}). To show that \idr{P n} holds whenever \idr{n}
    is even, it suffices to show:

    - \idr{P} holds for \idr{Z},

    - for any \idr{n}, if \idr{n} is even and \idr{P} holds for \idr{n}, then
      \idr{P} holds for \idr{S (S n)}.

As expected, we can apply \idr{ev_ind} directly instead of using `induction`. For
example, we can use it to show that \idr{Ev'} (the slightly awkward alternate
definition of evenness that we saw in an exercise in the `IndProp` chapter)
is equivalent to the cleaner inductive definition \idr{Ev}:

\todo[inline]{Copy here for now}

> data Ev' : Nat -> Type where
>   Ev'_0 : Ev' Z
>   Ev'_2 : Ev' 2
>   Ev'_sum : Ev' n -> Ev' m -> Ev' (n + m)

> ev_ev' : Ev n -> Ev' n
> ev_ev' {n} = ev_ind {P=Ev'}
>  Ev'_0
>  (\_, _, ev' => Ev'_sum Ev'_2 ev')
>  n

The precise form of a \idr{data} definition can affect the induction principle
Idris generates.

For example, in chapter `IndProp`, we defined ≤ as:

```idris
data Le : Nat -> Nat -> Type where
  Le_n : Le n n
  Le_S : Le n m -> Le n (S m)
```

This definition can be streamlined a little by observing that the left-hand
argument \idr{n} is the same everywhere in the definition, so we can actually
make it a "general parameter" to the whole definition, rather than an argument
to each constructor.

\todo[inline]{This doesn't seem to change anything}

> data Le : (n:Nat) -> Nat -> Type where
>   Le_n : Le n n
>   Le_S : Le n m -> Le n (S m)

> syntax [m] "<='" [n] = Le m n

The second one is better, even though it looks less symmetric. Why? Because it
gives us a simpler induction principle.

> le_ind : {n : Nat} -> {P : Nat -> Type} -> P n ->
>          ((m : Nat) -> (n <=' m) -> P m -> P (S m)) ->
>          ((n0 : Nat) -> (n <=' n0) -> P n0)
> le_ind {n=n0} pn _ n0 Le_n = pn
> le_ind pn f (S m) (Le_S le) = f m le (le_ind pn f m le)


== Formal vs. Informal Proofs by Induction

Question: What is the relation between a formal proof of a proposition \idr{P}
and an informal proof of the same proposition \idr{P}?

Answer: The latter should _teach_ the reader how to produce the former.

Question: How much detail is needed??

Unfortunately, there is no single right answer; rather, there is a range of
choices.

At one end of the spectrum, we can essentially give the reader the whole formal
proof (i.e., the "informal" proof will amount to just transcribing the formal
one into words). This may give the reader the ability to reproduce the formal
one for themselves, but it probably doesn't _teach_ them anything much.

At the other end of the spectrum, we can say "The theorem is true and you can
figure out why for yourself if you think about it hard enough." This is also not
a good teaching strategy, because often writing the proof requires one or more
significant insights into the thing we're proving, and most readers will give up
before they rediscover all the same insights as we did.

In the middle is the golden mean — a proof that includes all of the essential
insights (saving the reader the hard work that we went through to find the proof
in the first place) plus high-level suggestions for the more routine parts to
save the reader from spending too much time reconstructing these (e.g., what the
\idr{ih} says and what must be shown in each case of an inductive proof), but
not so much detail that the main ideas are obscured.

Since we've spent much of this chapter looking "under the hood" at formal proofs
by induction, now is a good moment to talk a little about _informal_ proofs by
induction.

\todo[inline]{Do we need 2 templates here?}

In the real world of mathematical communication, written proofs range from
extremely longwinded and pedantic to extremely brief and telegraphic. Although
the ideal is somewhere in between, while one is getting used to the style it is
better to start out at the pedantic end. Also, during the learning phase, it is
probably helpful to have a clear standard to compare against. With this in mind,
we offer two templates — one for proofs by induction over _data_ (i.e., where
the thing we're doing induction on lives in \idr{Type}) and one for proofs by
induction over _evidence_ (i.e., where the inductively defined thing lives in
\idr{Type}).


=== Induction Over an Inductively Defined Set

_Template_:

  - _Theorem_: <Universally quantified proposition of the form "For all
    \idr{n:s, P(n)}," where \idr{s} is some inductively defined set.>

    _Proof_: By induction on \idr{n}.

    <one case for each constructor \idr{c} of \idr{s}...>

    - Suppose \idr{n = c a1 ... ak}, where <...and here we state the \idr{IH}
      for each of the \idr{a}'s that has type \idr{s}, if any>. We must show
      <...and here we restate \idr{P(c a1 ... ak)}>.

      <go on and prove \idr{P(n)} to finish the case...>

    - <other cases similarly...> $\square$

_Example_:

  - _Theorem_: For all sets \idr{x}, lists \idr{l : List x}, and numbers
    \idr{n}, if \idr{length l = n} then \idr{index (S n) l = None}.

    _Proof_: By induction on \idr{l}.

    - Suppose \idr{l = []}. We must show, for all numbers \idr{n}, that, if
      \idr{length [] = n}, then \idr{index (S n) [] = None}.

      This follows immediately from the definition of \idr{index}.

    - Suppose \idr{l = x :: l'} for some \idr{x} and \idr{l'}, where
      \idr{length l' = n'} implies \idr{index (S n') l' = None}, for any number
      \idr{n'}. We must show, for all \idr{n}, that, if \idr{length (x::l') = n}
      then \idr{index (S n) (x::l') = None}.

      Let \idr{n} be a number with \idr{length l = n}. Since
      \idr{length l = length (x::l') = S (length l')},
      it suffices to show that
      \idr{index (S (length l')) l' = None}.
      But this follows directly from the induction hypothesis, picking \idr{n'}
      to be \idr{length l'}. $\square$


=== Induction Over an Inductively Defined Proposition

Since inductively defined proof objects are often called "derivation trees,"
this form of proof is also known as _induction on derivations_.

_Template_:

  - _Theorem_: <Proposition of the form "\idr{Q -> P}," where \idr{Q} is some inductively
    defined proposition (more generally, "For all \idr{x} \idr{y} \idr{z}, \idr{Q x y z -> P x y z}")>

    _Proof_: By induction on a derivation of \idr{Q}. <Or, more generally,
    "Suppose we are given \idr{x}, \idr{y}, and \idr{z}. We show that
    \idr{Q x y z} implies \idr{P x y z}, by induction on a derivation of
    \idr{Q x y z}"...>

    <one case for each constructor \idr{c} of \idr{Q}...>

      - Suppose the final rule used to show \idr{Q} is \idr{c}. Then <...and
        here we state the types of all of the \idr{a}'s together with any
        equalities that follow from the definition of the constructor and the IH
        for each of the \idr{a}'s that has type \idr{Q}, if there are any>. We
        must show <...and here we restate \idr{P}>.

        <go on and prove \idr{P} to finish the case...>

        <other cases similarly...> $\square$

_Example_

  - _Theorem_: The \idr{<=} relation is transitive — i.e., for all numbers
    \idr{n}, \idr{m}, and \idr{o}, if \idr{n <= m} and \idr{m <= o}, then
    \idr{n <= o}.

    _Proof_: By induction on a derivation of \idr{m <= o}.

      - Suppose the final rule used to show \idr{m <= o} is \idr{Le_n}. Then
        \idr{m = o} and we must show that \idr{n <= m}, which is immediate by
        hypothesis.

      - Suppose the final rule used to show \idr{m <= o} is \idr{Le_S}. Then
        \idr{o = S o'} for some \idr{o'} with \idr{m <= o'}. We must show that
        \idr{n <= S o'}. By induction hypothesis, \idr{n <= o'}.

        But then, by \idr{Le_S}, \idr{n <= S o'}. $\square$
