= Logic : Logic in Idris

> import Basics

> %hide Basics.Numbers.pred 
> %hide Basics.Playground2.plus

In previous chapters, we have seen many examples of factual claims
(_propositions_) and ways of presenting evidence of their truth (_proofs_). In
particular, we have worked extensively with equality propositions of the form
\idr{e1 = e2}, with implications (\idr{p -> q}), and with quantified
propositions (\idr{x -> P(x)}). In this chapter, we will see how Idris can be
used to carry out other familiar forms of logical reasoning. 

Before diving into details, let's talk a bit about the status of mathematical
statements in Idris. Recall that Idris is a _typed_ language, which means that
every sensible expression in its world has an associated type. Logical claims
are no exception: any statement we might try to prove in Idris has a type,
namely \idr{Type}, the type of _propositions_. We can see this with the \idr{:t}
command:

```idris
λΠ> :t 3 = 3
3 = 3 : Type
```

```idris
λΠ> :t (n, m : Nat) -> n + m = m + n
(n : Nat) -> (m : Nat) -> n + m = m + n : Type
```

Note that _all_ syntactically well-formed propositions have type \idr{Type} in
Idris, regardless of whether they are true or not.

Simply being a proposition is one thing; being provable is something else!

```idris
λΠ> :t (n : Nat) -> n = 2
(n : Nat) -> n = 2 : Type
```

```idris
λΠ> :t 3 = 4
3 = 4 : Type
```

Indeed, propositions don't just have types: they are _first-class objects_ that
can be manipulated in the same ways as the other entities in Idris's world. So
far, we've seen one primary place that propositions can appear: in functions'
type signatures.

> plus_2_2_is_4 : 2 + 2 = 4
> plus_2_2_is_4 = Refl

But propositions can be used in many other ways. For example, we can give a name
to a proposition as a value on its own, just as we have given names to
expressions of other sorts (you'll soon see why we start the name with a capital
letter). 

> Plus_fact : Type
> Plus_fact = 2+2=4

```idris
λΠ> :t Plus_fact
Plus_fact : Type
```

We can later use this name in any situation where a proposition is expected --
for example, in a function declaration.

> plus_fact_is_true : Plus_fact
> plus_fact_is_true = Refl

(Here's the reason - recall that names starting with lowercase letters are
considered implicits in Idris, so \idr{plus_fact} would be considered a free
variable!)

We can also write _parameterized_ propositions -- that is, functions that take
arguments of some type and return a proposition. For instance, the following
function takes a number and returns a proposition asserting that this number is
equal to three:

> is_three : Nat -> Type 
> is_three n = n=3

```idris
λΠ> :t is_three
is_three : Nat -> Type
```

In Idris, functions that return propositions are said to define _properties_ of
their arguments.

For instance, here's a (polymorphic) property defining the familiar notion of an
_injective function_.

> injective : (f : a -> b) -> Type
> injective {a} {b} f = (x, y : a) -> f x = f y -> x = y

> succ_inj : injective S
> succ_inj x x Refl = Refl

The equality operator \idr{=} is also a function that returns a \idr{Type}.

The expression \idr{n = m} is syntactic sugar for \idr{(=) n m}, defined
internally in Idris. Because \idr{=} can be used with elements of any type, it
is also polymorphic:

```idris
λΠ> :t (=)
(=) : A -> B -> Type
```


== Logical Connectives

=== Conjunction

The _conjunction_ (or _logical and_) of propositions \idr{a} and \idr{b} in
Idris is the same as the pair of \idr{a} and \idr{b}, written \idr{(a, b)},
representing the claim that both \idr{a} and \idr{b} are true.

> and_example : (3 + 4 = 7, 2 * 2 = 4)

To prove a conjunction, we can use value-level pair syntax:

> and_example = (Refl, Refl)

For any propositions \idr{a} and \idr{b}, if we assume that \idr{a} is true and
we assume that \idr{a} is true, we can trivially conclude that \idr{(a,b)} is
also true.

> and_intro : a -> b -> (a, b)
> and_intro = MkPair


==== Exercise: 2 stars (and_exercise)

> and_exercise : (n, m : Nat) -> n + m = 0 -> (n = 0, m = 0)
> and_exercise n m prf = ?and_exercise_rhs

$\square$

So much for proving conjunctive statements. To go in the other direction --
i.e., to _use_ a conjunctive hypothesis to help prove something else -- we
employ pattern matching.


If the proof context contains a hypothesis \idr{h} of the form \idr{(a,b)}, case
splitting will replace it with a pair pattern \idr{(a,b)}.

> and_example2 : (n, m : Nat) -> (n = 0, m = 0) -> n + m = 0
> and_example2 Z Z (Refl,Refl) = Refl
> and_example2 (S _) _ (Refl,_) impossible
> and_example2 _ (S _) (_,Refl) impossible

You may wonder why we bothered packing the two hypotheses \idr{n = 0} and \idr{m
= 0} into a single conjunction, since we could have also stated the theorem with
two separate premises:

> and_example2'' : (n, m : Nat) -> n = 0 -> m = 0 -> n + m = 0
> and_example2'' Z Z Refl Refl = Refl
> and_example2'' (S _) _ Refl _ impossible
> and_example2'' _ (S _) _ Refl impossible

For this theorem, both formulations are fine. But it's important to understand
how to work with conjunctive hypotheses because conjunctions often arise from
intermediate steps in proofs, especially in bigger developments. Here's a simple
example:

> and_example3 : (n, m : Nat) -> n + m = 0 -> n * m = 0
> and_example3 n m prf = 
>  let (nz, _) = and_exercise n m prf in 
>  rewrite nz in Refl

\todo[inline]{Remove lemma and exercise, use \idr{fst} and \idr{snd} directly?}

Another common situation with conjunctions is that we know \idr{(a,b)} but in
some context we need just \idr{a} (or just \idr{b}). The following lemmas are
useful in such cases:

> proj1 : (p, q) -> p
> proj1 = fst


==== Exercise: 1 star, optional (proj2)

> proj2 : (p, q) -> q
> proj2 x = ?proj2_rhs

$\square$

Finally, we sometimes need to rearrange the order of conjunctions and/or the
grouping of multi-way conjunctions. The following commutativity and
associativity theorems are handy in such cases.

> and_commut : (p, q) -> (q, p)
> and_commut (p, q) = (q, p)


==== Exercise: 2 stars (and_assoc)

\todo[inline]{Remove or demote to 1 star?}

> and_assoc : (p, (q, r)) -> ((p, q), r)
> and_assoc x = ?and_assoc_rhs

$\square$


=== Disjunction

\todo[inline]{Make syntax synonym?}

Another important connective is the _disjunction_, or _logical or_ of two
propositions: \idr{a `Either` b} is true when either \idr{a} or \idr{b} is. The
first case has be tagged with \idr{Left}, and the second with \idr{Right}.

To use a disjunctive hypothesis in a proof, we proceed by case analysis, which,
as for \idr{Nat} or other data types, can be done with pattern matching. Here is
an example:

> or_example : (n, m : Nat) -> ((n = 0) `Either` (m = 0)) -> n * m = 0
> or_example Z _ (Left Refl) = Refl
> or_example (S _) _ (Left Refl) impossible
> or_example n Z (Right Refl) = multZeroRightZero n
> or_example _ (S _) (Right Refl) impossible

Conversely, to show that a disjunction holds, we need to show that one of its
sides does. This can be done via aforementioned \idr{Left} and \idr{Right}
constructors. Here is a trivial use...

> or_intro : a -> a `Either` b
> or_intro = Left

... and a slightly more interesting example requiring both \idr{Left} and
\idr{Right}:

> zero_or_succ : (n : Nat) -> ((n = 0) `Either` (n = S (pred n)))
> zero_or_succ Z = Left Refl
> zero_or_succ (S _) = Right Refl


==== Exercise: 1 star (mult_eq_0)

> mult_eq_0 : n * m = 0 -> ((n = 0) `Either` (m = 0))
> mult_eq_0 prf = ?mult_eq_0_rhs

$\square$


==== Exercise: 1 star (or_commut)

> or_commut : (p `Either` q) -> (q `Either` p)
> or_commut x = ?or_commut_rhs

$\square$


=== Falsehood and Negation

So far, we have mostly been concerned with proving that certain things are
_true_ -- addition is commutative, appending lists is associative, etc. Of
course, we may also be interested in _negative_ results, showing that certain
propositions are _not_ true. In Idris, such negative statements are expressed
with the negation typelevel function \idr{Not}.

To see how negation works, recall the discussion of the _principle of explosion_
from the previous chapter; it asserts that, if we assume a contradiction, then
any other proposition can be derived. Following this intuition, we could define
\idr{Not p} as \idr{q -> (p -> q)}. Idris actually makes a slightly different
choice, defining \idr{Not p} as \idr{p -> Void}, where \idr{Void} is a
_particular_ contradictory proposition defined in the standard library.

\todo[inline]{Edit}

Module MyNot.

Definition not (P:Type) := P -> Void.

Notation "¬ x" := (not x) : type_scope.

```idris
λΠ> :t Not
Not : Type -> Type
```

Since \idr{Void} is a contradictory proposition, the principle of explosion also
applies to it. If we get \idr{Void} into the proof context, we can call
\idr{absurd} on it to complete any goal:

> ex_falso_quodlibet : Void -> p
> ex_falso_quodlibet = absurd

The Latin _ex falso quodlibet_ means, literally, "from falsehood follows
whatever you like"; this is another common name for the principle of explosion.


==== Exercise: 2 stars, optional (not_implies_our_not)

Show that Idris's definition of negation implies the intuitive one mentioned
above:

> not_implies_our_not : Not p -> (q -> (p -> q))
> not_implies_our_not notp q p = ?not_implies_our_not_rhs

$\square$

This is how we use \idr{Not} to state that \idr{0} and \idr{1} are different
elements of \idr{Nat}:

\todo[inline]{Explain \idr{Refl}-lambda syntax and \idr{Uninhabited}}

> zero_not_one : Not (Z = S _)
> zero_not_one = \Refl impossible

We could also rely on the \idr{Uninhabited} instance in stdlib and write this as

```idris
zero_not_one = uninhabited
```

It takes a little practice to get used to working with negation in Idris. Even
though you can see perfectly well why a statement involving negation is true, it
can be a little tricky at first to get things into the right configuration so
that Idris can understand it! Here are proofs of a few familiar facts to get you
warmed up.

> not_False : Not Void
> not_False = absurd

> contradiction_implies_anything : (p, Not p) -> q
> contradiction_implies_anything (p, notp) = absurd $ notp p

> double_neg : p -> Not $ Not p
> double_neg p notp = notp p


==== Exercise: 2 stars, advanced, recommendedM (double_neg_inf)

Write an informal proof of \idr{double_neg}:

_Theorem_: \idr{p} implies \idr{Not $ Not p}, for any proposition \idr{p}.

> -- FILL IN HERE 

$\square$


==== Exercise: 2 stars, recommended (contrapositive)

> contrapositive : (p -> q) -> (Not q -> Not p)
> contrapositive pq = ?contrapositive_rhs

$\square$


==== Exercise: 1 star (not_both_true_and_false)

> not_both_true_and_false : Not (p, Not p)
> not_both_true_and_false = ?not_both_true_and_false_rhs

$\square$


==== Exercise: 1 star, advancedM (informal_not_PNP)

Write an informal proof (in English) of the proposition \idr{Not (p, Not p)}.

> -- FILL IN HERE 

$\square$

Similarly, since inequality involves a negation, it requires a little practice
to be able to work with it fluently. Here is one useful trick. If you are trying
to prove a goal that is nonsensical (e.g., the goal state is \idr{False =
True}), apply \idr{absurd} to change the goal to \idr{Void}. This makes it
easier to use assumptions of the form \idr{Not p} that may be available in the
context -- in particular, assumptions of the form \idr{Not (x=y)}.

> not_true_is_false : (b : Bool) -> Not (b = True) -> b = False
> not_true_is_false False h = Refl
> not_true_is_false True h = absurd $ h Refl


=== Truth

Besides \idr{Void}, Idris's standard library also defines \idr{Unit}, a proposition that is
trivially true. To prove it, we use the predefined constant \idr{()}:

> True_is_true : Unit
> True_is_true = ()

Unlike \idr{Void}, which is used extensively, \idr{Unit} is used quite rarely in
proofs, since it is trivial (and therefore uninteresting) to prove as a goal,
and it carries no useful information as a hypothesis. But it can be quite useful
when defining complex proofs using conditionals or as a parameter to
higher-order proofs. We will see examples of such uses of \idr{Unit} later on.


=== Logical Equivalence

The handy "if and only if" connective, which asserts that two propositions have
the same truth value, is just the conjunction of two implications.

> namespace MyIff

>   iff : {p,q : Type} -> Type
>   iff {p} {q} = (p -> q, q -> p)

Idris' stdlib has a more general form of this, \idr{Iso}, in
\idr{Control.Isomorphism}.

>   syntax [p] "<->" [q] = iff {p} {q}

>   iff_sym : (p <-> q) -> (q <-> p)
>   iff_sym (pq, qp) = (qp, pq)


>   not_true_iff_false : (Not (b = True)) <-> (b = False)
>   not_true_iff_false {b} = (not_true_is_false b, not_true_and_false b)
>   where
>     not_true_and_false : (b : Bool) -> (b = False) -> (b = True) -> Void
>     not_true_and_false False _ Refl impossible
>     not_true_and_false True Refl _ impossible


==== Exercise: 1 star, optional (iff_properties)

Using the above proof that \idr{<->} is symmetric (\idr{iff_sym}) as a guide,
prove that it is also reflexive and transitive.

>   iff_refl : p <-> p
>   iff_refl = ?iff_refl_rhs

>   iff_trans : (p <-> q) -> (q <-> r) -> (p <-> r)
>   iff_trans piq qir = ?iff_trans_rhs

$\square$


==== Exercise: 3 stars (or_distributes_over_and)

>   or_distributes_over_and : (p `Either` (q,r)) <-> (p `Either` q, p `Either` r)
>   or_distributes_over_and = ?or_distributes_over_and_rhs

$\square$

\todo[inline]{Edit, what to do wth Setoids?}

Some of Idris's tactics treat iff statements specially, avoiding the need for
some low-level proof-state manipulation. In particular, rewrite and reflexivity
can be used with iff statements, not just equalities. To enable this behavior,
we need to import a special Idris library that allows rewriting with other
formulas besides equality:

Require Import Idris.Setoids.Setoid.

Here is a simple example demonstrating how these tactics work with iff. First,
let's prove a couple of basic iff equivalences...

>   mult_0 : (n * m = Z) <-> ((n = Z) `Either` (m = Z))
>   mult_0 {n} {m} = (to n m, or_example n m)
>   where
>     to : (n, m : Nat) -> (n * m = Z) -> (n = 0) `Either` (m = 0)
>     to Z _ Refl = Left Refl
>     to (S _) Z _ = Right Refl
>     to (S _) (S _) Refl impossible

>   or_assoc : (p `Either` (q `Either` r)) <-> ((p `Either` q) `Either` r)
>   or_assoc = (to, fro)
>   where
>     to : Either p (Either q r) -> Either (Either p q) r
>     to (Left p) = Left $ Left p
>     to (Right (Left q)) = Left $ Right q
>     to (Right (Right r)) = Right r
>     fro : Either (Either p q) r -> Either p (Either q r)
>     fro (Left (Left p)) = Left p
>     fro (Left (Right q)) = Right $ Left q
>     fro (Right r) = Right $ Right r

We can now use these facts with rewrite and reflexivity to give smooth proofs of
statements involving equivalences. Here is a ternary version of the previous
mult_0 result:

>     mult_0_3 : (n * m * p = 0) <-> 
>                ((n = 0) `Either` ((m = 0) `Either` (p = 0)))

Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

The apply tactic can also be used with ↔. When given an equivalence as its
argument, apply tries to guess which side of the equivalence to use.

>    apply_iff_example : (n, m : Nat) -> n * m = 0 -> ((n = 0) `Either` (m = 0))

Proof.
  intros n m H. apply mult_0. apply H.
Qed.


=== Existential Quantification

Another important logical connective is existential quantification. To say that
there is some \idr{x} of type \idr{t} such that some property \idr{p} holds of
\idr{x}, we write \idr{(x : t ** p)}. The type annotation \idr{: t} can be
omitted if Idris is able to infer from the context what the type of \idr{x}
should be.

\todo[inline]{Edit}

To prove a statement of the form \idr{(x ** p)}, we must show that \idr{p} holds
for some specific choice of value for \idr{x}, known as the _witness_ of the
existential. This is done in two steps: First, we explicitly tell Idris which
witness \idr{t} we have in mind by writing it on the left side of \idr{**}. Then
we prove that \idr{p} holds after all occurrences of \idr{x} are replaced by
\idr{t}.

> four_is_even : (n : Nat ** 4 = n + n)
> four_is_even = (2 ** Refl)

Conversely, if we have an existential hypothesis \idr{(x ** p)} in the context,
we can pattern match on it to obtain a witness \idr{x} and a hypothesis stating
that \idr{p} holds of \idr{x}.

> exists_example_2 : (m : Nat ** n = 4 + m) -> (o : Nat ** n = 2 + o)
> exists_example_2 (m ** pf) = (2 + m ** pf)


==== Exercise: 1 star (dist_not_exists)

Prove that "\idr{p} holds for all \idr{x}" implies "there is no \idr{x} for
which \idr{p} does not hold."

> dist_not_exists : {p : a -> Type} -> ((x:a) -> p x) -> Not (x ** Not $ p x)
> dist_not_exists f = ?dist_not_exists_rhs

$\square$


==== Exercise: 2 stars (dist_exists_or)

Prove that existential quantification distributes over disjunction.

> dist_exists_or : (p, q : a -> Type) -> (x ** (p x `Either` q x)) <-> 
>                                       ((x ** p x) `Either` (x ** q x))
> dist_exists_or p q = ?dist_exists_or_rhs

$\square$

== Programming with Propositions

The logical connectives that we have seen provide a rich vocabulary for defining
complex propositions from simpler ones. To illustrate, let's look at how to
express the claim that an element \idr{x} occurs in a list \idr{l}. Notice that
this property has a simple recursive structure:

  - If \idr{l} is the empty list, then \idr{x} cannot occur on it, so the
    property "\idr{x} appears in \idr{l}" is simply false.

  - Otherwise, \idr{l} has the form \idr{x' :: xs}. In this case, \idr{x} occurs
    in \idr{l} if either it is equal to \idr{x'} or it occurs in \idr{xs}.

We can translate this directly into a straightforward recursive function from
taking an element and a list and returning a proposition:

> In : (x : a) -> (l : List a) -> Type
> In x [] = Void
> In x (x' :: xs) = (x' = x) `Either` In x xs

When \idr{In} is applied to a concrete list, it expands into a concrete sequence
of nested disjunctions.

> In_example_1 : In 4 [1, 2, 3, 4, 5]
> In_example_1 = Right $ Right $ Right $ Left Refl

> In_example_2 : In n [2, 4] -> (n' : Nat ** n = 2 * n')
> In_example_2 (Left Refl) = (1 ** Refl)
> In_example_2 (Right $ Left Refl) = (2 ** Refl)
> In_example_2 (Right $ Right prf) = absurd prf

(Notice the use of \idr{absurd} to discharge the last case.)

We can also prove more generic, higher-level lemmas about \idr{In}.

Note, in the next, how \idr{In} starts out applied to a variable and only gets
expanded when we do case analysis on this variable:

> In_map : (f : a -> b) -> (l : List a) -> (x : a) -> In x l -> 
>          In (f x) (map f l)
> In_map _ [] _ ixl = absurd ixl
> In_map f (x' :: xs) x (Left prf) = rewrite prf in Left Refl
> In_map f (x' :: xs) x (Right r) = Right $ In_map f xs x r

This way of defining propositions recursively, though convenient in some cases,
also has some drawbacks. In particular, it is subject to Idris's usual
restrictions regarding the definition of recursive functions, e.g., the
requirement that they be "obviously terminating." In the next chapter, we will
see how to define propositions _inductively_, a different technique with its own
set of strengths and limitations.


==== Exercise: 2 stars (In_map_iff)

> In_map_iff : (f : a -> b) -> (l : List a) -> (y : b) -> 
>              (In y (map f l)) <-> (x ** (f x = y, In x l))
> In_map_iff f l y = ?In_map_iff_rhs

$\square$


==== Exercise: 2 stars (in_app_iff)

> in_app_iff : (In a (l++l')) <-> (In a l `Either` In a l')
> in_app_iff = ?in_app_iff_rhs

$\square$


==== Exercise: 3 stars (All)

Recall that functions returning propositions can be seen as _properties_ of
their arguments. For instance, if \idr{p} has type \idr{Nat -> Type}, then
\idr{p n} states that property \idr{p} holds of \idr{n}.

Drawing inspiration from \idr{In}, write a recursive function \idr{All} stating
that some property \idr{p} holds of all elements of a list \idr{l}. To make sure
your definition is correct, prove the \idr{All_In} lemma below. (Of course, your
definition should _not_ just restate the left-hand side of \idr{All_In}.)

> All : (p : t -> Type) -> (l : List t) -> Type
> All p l = ?All_rhs

> All_In : (p : t -> Type) -> (l : List t) -> 
>          ((x:t) -> In x l -> p x) <-> (All p l)
> All_In P l = ?All_In_rhs

$\square$


==== Exercise: 3 stars (combine_odd_even)

Complete the definition of the \idr{combine_odd_even} function below. It takes
as arguments two properties of numbers, \idr{podd} and \idr{peven}, and it
should return a property \idr{p} such that \idr{p n} is equivalent to \idr{podd
n} when \idr{n} is odd and equivalent to \idr{peven n} otherwise.

> combine_odd_even : (podd, peven : Nat -> Type) -> (Nat -> Type)
> combine_odd_even podd peven = ?combine_odd_even_rhs

To test your definition, prove the following facts:

> combine_odd_even_intro : (podd, peven : Nat -> Type) -> (n : Nat) ->
>                          (oddb n = True -> podd n) ->
>                          (oddb n = False -> peven n) ->
>                          combine_odd_even podd peven n
> combine_odd_even_intro podd peven n oddp evenp = ?combine_odd_even_intro_rhs

> combine_odd_even_elim_odd : (podd, peven : Nat -> Type) -> (n : Nat) ->
>                             combine_odd_even podd peven n ->
>                             oddb n = True ->
>                             podd n
> combine_odd_even_elim_odd podd peven n x prf = ?combine_odd_even_elim_odd_rhs

> combine_odd_even_elim_even : (podd, peven : Nat -> Type) -> (n : Nat) ->
>                              combine_odd_even podd peven n ->
>                              oddb n = False ->
>                              peven n
> combine_odd_even_elim_even podd peven n x prf = ?combine_odd_even_elim_even_rhs

$\square$


== Applying Theorems to Arguments

One feature of Idris that distinguishes it from many other proof assistants is
that it treats _proofs_ as first-class objects.

There is a great deal to be said about this, but it is not necessary to
understand it in detail in order to use Idris. This section gives just a taste,
while a deeper exploration can be found in the optional chapters
`ProofObjects` and `IndPrinciples`.

We have seen that we can use the \idr{:t} command to ask Idris to print the type
of an expression. We can also use \idr{:t} to ask what theorem a particular
identifier refers to.

```idris
λΠ> :t plusCommutative
plusCommutative : (left : Nat) -> (right : Nat) -> left + right = right + left
```

Idris prints the _statement_ of the \idr{plusCommutative} theorem in the same
way that it prints the _type_ of any term that we ask it to check. Why?

The reason is that the identifier \idr{plusCommutative} actually refers to a
_proof object_ -- a data structure that represents a logical derivation
establishing of the truth of the statement \idr{(n, m : Nat) -> n + m = m + n}.
The type of this object _is_ the statement of the theorem that it is a proof of.

Intuitively, this makes sense because the statement of a theorem tells us what
we can use that theorem for, just as the type of a computational object tells us
what we can do with that object -- e.g., if we have a term of type \idr{Nat ->
Nat -> Nat}, we can give it two \idr{Nat}s as arguments and get a \idr{Nat}
back. Similarly, if we have an object of type \idr{n = m -> n + n = m + m} and
we provide it an "argument" of type \idr{n = m}, we can derive \idr{n + n = m +
m}.

Operationally, this analogy goes even further: by applying a theorem, as if it
were a function, to hypotheses with matching types, we can specialize its result
without having to resort to intermediate assertions. For example, suppose we
wanted to prove the following result:

> plus_comm3 : (n, m, p : Nat) -> n + (m + p) = (p + m) + n

\todo[inline]{Edit, we already have done this before}

It appears at first sight that we ought to be able to prove this by rewriting
with \idr{plusCommutative} twice to make the two sides match. The problem, however, is that
the second \idr{rewrite} will undo the effect of the first.

Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite plus_comm.
  (* We are back where we started... *)
Abort.

One simple way of fixing this problem, using only tools that we already know, is
to use assert to derive a specialized version of plus_comm that can be used to
rewrite exactly where we want.

Lemma plus_comm3_take2 :
  ∀n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  assert (H : m + p = p + m).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

A more elegant alternative is to apply plus_comm directly to the arguments we
want to instantiate it with, in much the same way as we apply a polymorphic
function to a type argument.

> plus_comm3 n m p = rewrite plusCommutative n (m+p) in 
>                    rewrite plusCommutative m p in Refl

You can "use theorems as functions" in this way with almost all tactics that
take a theorem name as an argument. Note also that theorem application uses the
same inference mechanisms as function application; thus, it is possible, for
example, to supply wildcards as arguments to be inferred, or to declare some
hypotheses to a theorem as implicit by default. These features are illustrated
in the proof below.

> lemma_application_ex : (n : Nat) -> (ns : List Nat) -> 
>                        In n (map (\m => m * 0) ns) -> n = 0
> lemma_application_ex _ [] prf = absurd prf
> lemma_application_ex _ (y :: _) (Left prf) = rewrite sym $ multZeroRightZero y in sym prf
> lemma_application_ex n (_ :: xs) (Right prf) = lemma_application_ex n xs prf

We will see many more examples of the idioms from this section in later chapters.


== Idris vs. Set Theory

\todo[inline]{Edit}

Idris's logical core, the Calculus of Inductive Constructions, differs in some
important ways from other formal systems that are used by mathematicians for
writing down precise and rigorous proofs. For example, in the most popular
foundation for mainstream paper-and-pencil mathematics, Zermelo-Fraenkel Set
Theory (ZFC), a mathematical object can potentially be a member of many
different sets; a term in Idris's logic, on the other hand, is a member of at
most one type. This difference often leads to slightly different ways of
capturing informal mathematical concepts, but these are, by and large, quite
Natural and easy to work with. For example, instead of saying that a natural
number \idr{n} belongs to the set of even numbers, we would say in Idris that
\idr{ev n} holds, where \idr{ev : Nat -> Type} is a property describing even
numbers.

However, there are some cases where translating standard mathematical reasoning
into Idris can be either cumbersome or sometimes even impossible, unless we
enrich the core logic with additional axioms. We conclude this chapter with a
brief discussion of some of the most significant differences between the two
worlds.


=== Functional Extensionality

The equality assertions that we have seen so far mostly have concerned elements
of inductive types (\idr{Nat}, \idr{Bool}, etc.). But since Idris's equality
operator is polymorphic, these are not the only possibilities -- in particular,
we can write propositions claiming that two _functions_ are equal to each other:

> function_equality_ex1 : plus 3 = plus (pred 4)
> function_equality_ex1 = Refl

In common mathematical practice, two functions `f` and `g` are considered equal
if they produce the same outputs:
    
    `(∀x, f x = g x) -> f = g`

This is known as the principle of _functional extensionality_.

Informally speaking, an "extensional property" is one that pertains to an
object's observable behavior. Thus, functional extensionality simply means that
a function's identity is completely determined by what we can observe from it --
i.e., in Idris terms, the results we obtain after applying it.

Functional extensionality is not part of Idris's basic axioms. This means that
some "reasonable" propositions are not provable.

```idris
function_equality_ex2 : (\x => plus x 1) = (\x => plus 1 x)
function_equality_ex2 = ?stuck
```

\todo[inline]{Edit, use \idr{really_believe_me}?}

However, we can add functional extensionality to Idris's core logic using the
Axiom command.

Axiom functional_extensionality : ∀{X Y: Type}
                                   {f g : X -> Y},
  (∀(x:X), f x = g x) -> f = g.

Using Axiom has the same effect as stating a theorem and skipping its proof
using Admitted, but it alerts the reader that this isn't just something we're
going to come back and fill in later!

We can now invoke functional extensionality in proofs:

Example function_equality_ex2 :
  (fun x ⇒ plus x 1) = (fun x ⇒ plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

Naturally, we must be careful when adding new axioms into Idris's logic, as they
may render it inconsistent -- that is, they may make it possible to prove every
proposition, including Void!

Unfortunately, there is no simple way of telling whether an axiom is safe to
add: hard work is generally required to establish the consistency of any
particular combination of axioms.

However, it is known that adding functional extensionality, in particular, is
consistent.

To check whether a particular proof relies on any additional axioms, use the
Print Assumptions command.

Print Assumptions function_equality_ex2.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)


==== Exercise: 4 stars (tr_rev)

One problem with the definition of the list-reversing function \idr{rev} that we
have is that it performs a call to \idr{++} on each step; running \idr{++} takes
time asymptotically linear in the size of the list, which means that \idr{rev}
has quadratic running time. 

> rev : (l : List x) -> List x
> rev [] = []
> rev (h::t) = (rev t) ++ [h]

We can improve this with the following definition:

> rev_append : (l1, l2 : List x) -> List x
> rev_append [] l2 = l2
> rev_append (x :: xs) l2 = rev_append xs (x :: l2)

> tr_rev : (l : List x) -> List x
> tr_rev l = rev_append l []

(This is very similar to how \idr{reverse} is defined in \idr{Prelude.List}.)

This version is said to be _tail-recursive_, because the recursive call to the
function is the last operation that needs to be performed (i.e., we don't have
to execute \idr{++} after the recursive call); a decent compiler will generate
very efficient code in this case. Prove that the two definitions are indeed
equivalent.

> tr_rev_correct : tr_rev x = rev x
> tr_rev_correct = ?tr_rev_correct_rhs

$\square$


=== Propositions and Booleans

We've seen two different ways of encoding logical facts in Idris: with
_booleans_ (of type \idr{Bool}), and with _propositions_ (of type \idr{Type}).

For instance, to claim that a number \idr{n} is even, we can say either

  - (1) that \idr{evenb n} returns \idr{True}, or

  - (2) that there exists some \idr{k} such that \idr{n = double k}. Indeed,
    these two notions of evenness are equivalent, as can easily be shown with a
    couple of auxiliary lemmas.

We often say that the boolean \idr{evenb n} _reflects_ the proposition \idr{(k
** n = double k)}.

> double : (n : Nat) -> Nat      
> double  Z    = Z               
> double (S k) = S (S (double k))

> evenb_double : evenb (double k) = True
> evenb_double {k = Z} = Refl
> evenb_double {k = (S k')} = evenb_double {k=k'}


==== Exercise: 3 stars (evenb_double_conv)

> evenb_double_conv : (k ** n = if evenb n then double k else S (double k))
> -- Hint: Use the \idr{evenb_S} lemma from `Induction`
> evenb_double_conv = ?evenb_double_conv_rhs

$\square$

\todo[inline]{Finish, use \idr{really_believe_me} for \idr{evenb_double_conv}?}

> even_bool_prop : (evenb n = True) <-> (k ** n = double k)
> even_bool_prop = ?even_bool_prop_rhs

Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. ∃k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Similarly, to state that two numbers \idr{n} and \idr{m} are equal, we can say
either (1) that \idr{beq_nat n m} returns \idr{True} or (2) that \idr{n = m}.
These two notions are equivalent.

\todo[inline]{Finish, implement \idr{beq_nat_true} and \idr{beq_nat_refl} from
`Tactics`}

> beq_nat_true_iff : (n1, n2 : Nat) -> (beq_nat n1 n2 = True) <-> (n1 = n2)
> beq_nat_true_iff n1 n2 = ?beq_nat_true_iff_rhs

Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite ← beq_nat_refl. reflexivity.
Qed.

However, while the boolean and propositional formulations of a claim are
equivalent from a purely logical perspective, they need not be equivalent
_operationally_. Equality provides an extreme example: knowing that \idr{beq_nat
n m = True} is generally of little direct help in the middle of a proof
involving \idr{n} and \idr{m}; however, if we convert the statement to the
equivalent form \idr{n = m}, we can rewrite with it.

The case of even numbers is also interesting. Recall that, when proving the
backwards direction of \idr{even_bool_prop} (i.e., \idr{evenb_double}, going
from the propositional to the boolean claim), we used a simple induction on
\idr{k}. On the other hand, the converse (the \idr{evenb_double_conv} exercise)
required a clever generalization, since we can't directly prove \idr{(k ** n =
double k) -> evenb n = True}.

For these examples, the propositional claims are more useful than their boolean
counterparts, but this is not always the case. For instance, we cannot test
whether a general proposition is true or not in a function definition; as a
consequence, the following code fragment is rejected:

```idris
is_even_prime : Nat -> Bool
is_even_prime n = if n = 2 then True else False
```

Idris complains that \idr{n = 2} has type \idr{Type}, while it expects an
element of \idr{Bool} (or some other inductive type with two elements). The
reason for this error message has to do with the _computational_ nature of
Idris's core language, which is designed so that every function that it can
express is computable and total. One reason for this is to allow the extraction
of executable programs from Idris developments. As a consequence, \idr{Type} in
Idris does _not_ have a universal case analysis operation telling whether any
given proposition is true or Void, since such an operation would allow us to
write non-computable functions.

Although general non-computable properties cannot be phrased as boolean
computations, it is worth noting that even many _computable_ properties are
easier to express using \idr{Type} than \idr{Bool}, since recursive function
definitions are subject to significant restrictions in Idris. For instance, the
next chapter shows how to define the property that a regular expression matches
a given string using \idr{Type}. Doing the same with \idr{Bool} would amount to
writing a regular expression matcher, which would be more complicated, harder to
understand, and harder to reason about.

Conversely, an important side benefit of stating facts using booleans is
enabling some proof automation through computation with Idris terms, a technique
known as _proof by reflection_. Consider the following statement:

> even_1000 : (k ** 1000 = double k)

The most direct proof of this fact is to give the value of \idr{k} explicitly.

> even_1000 = (500 ** Refl)

On the other hand, the proof of the corresponding boolean statement is even
simpler:

> even_1000' : evenb 1000 = True
> even_1000' = Refl

What is interesting is that, since the two notions are equivalent, we can use
the boolean formulation to prove the other one without mentioning the value 500
explicitly:

\todo[inline]{Finish with \idr{even_bool_prop}}

> even_1000'' : (k ** 1000 = double k)
> even_1000'' = ?even_1000'_rhs

Proof. apply even_bool_prop. reflexivity. Qed.

Although we haven't gained much in terms of proof size in this case, larger
proofs can often be made considerably simpler by the use of reflection. As an
extreme example, the Coq proof of the famous _4-color theorem_ uses reflection
to reduce the analysis of hundreds of different cases to a boolean computation.
We won't cover reflection in great detail, but it serves as a good example
showing the complementary strengths of booleans and general propositions.


==== Exercise: 2 stars (logical_connectives)

The following lemmas relate the propositional connectives studied in this
chapter to the corresponding boolean operations.

> andb_true_iff : (b1, b2 : Bool) -> (b1 && b2 = True) <-> 
>                                    (b1 = True, b2 = True)
> andb_true_iff b1 b2 = ?andb_true_iff_rhs

> orb_true_iff : (b1, b2 : Bool) -> (b1 || b2 = True) <-> 
>                                   ((b1 = True) `Either` (b2 = True))
> orb_true_iff b1 b2 = ?orb_true_iff_rhs

$\square$


==== Exercise: 1 star (beq_Nat_false_iff)

The following theorem is an alternate "negative" formulation of
\idr{beq_nat_true_iff} that is more convenient in certain situations (we'll see
examples in later chapters).

> beq_nat_false_iff : (x, y : Nat) -> (beq_nat x y = False) <-> (Not (x = y))
> beq_nat_false_iff x y = ?beq_nat_false_iff_rhs

$\square$


==== Exercise: 3 stars (beq_list)

Given a boolean operator \idr{beq} for testing equality of elements of some type
\idr{a}, we can define a function \idr{beq_list beq} for testing equality of
lists with elements in \idr{a}. Complete the definition of the \idr{beq_list}
function below. To make sure that your definition is correct, prove the lemma
\idr{beq_list_true_iff}.

> beq_list : (beq : a -> a -> Bool) -> (l1, l2 : List a) -> Bool
> beq_list beq l1 l2 = ?beq_list_rhs

> beq_list_true_iff : (beq : a -> a -> Bool) -> 
>                     ((a1, a2 : a) -> (beq a1 a2 = True) <-> (a1 = a2)) ->
>       ((l1, l2 : List a) -> (beq_list beq l1 l2 = True) <-> (l1 = l2))

$\square$


==== Exercise: 2 stars, recommended (All_forallb)

Recall the function \idr{forallb}, from the exercise
\idr{forall_exists_challenge} in chapter `Tactics`:

> forallb : (test : x -> Bool) -> (l : List x) -> Bool
> forallb _ [] = True
> forallb test (x :: xs) = test x && forallb test xs
  
Prove the theorem below, which relates \idr{forallb} to the \idr{All} property
of the above exercise.

> forallb_true_iff : (l : List x) -> (forallb test l = True) <-> 
>                                    (All (\x => test x = True) l)
> forallb_true_iff l = ?forallb_true_iff_rhs

Are there any important properties of the function \idr{forallb} which are not
captured by this specification?

> -- FILL IN HERE 

$\square$


=== Classical vs. Constructive Logic

We have seen that it is not possible to test whether or not a proposition
\idr{p} holds while defining a Idris function. You may be surprised to learn
that a similar restriction applies to _proofs_! In other words, the following
intuitive reasoning principle is not derivable in Idris:

```idris
excluded_middle : p `Either` (Not p)
```

To understand operationally why this is the case, recall that, to prove a
statement of the form \idr{p `Either` q}, we use the \idr{Left} and \idr{Right}
pattern matches, which effectively require knowing which side of the disjunction
holds. But the universally quantified \idr{p} in \idr{excluded_middle} is an
arbitrary proposition, which we know nothing about. We don't have enough
information to choose which of \idr{Left} or \idr{Right} to apply, just as Idris
doesn't have enough information to mechanically decide whether \idr{p} holds or
not inside a function.

However, if we happen to know that \idr{p} is reflected in some boolean term
\idr{b}, then knowing whether it holds or not is trivial: we just have to check
the value of \idr{b}.

\todo[inline]{Remove when a release with
https://github.com/idris-lang/Idris-dev/pull/3925 happens}

> Uninhabited (False = True) where
>   uninhabited Refl impossible

\todo[inline]{Explain `uninhabited`}

> restricted_excluded_middle : (p <-> b = True) -> p `Either` Not p
> restricted_excluded_middle {b = True} (_, bp) = Left $ bp Refl
> restricted_excluded_middle {b = False} (pb, _) = Right $ uninhabited . pb

In particular, the excluded middle is valid for equations \idr{n = m}, between
natural numbers \idr{n} and \idr{m}.

\todo[inline]{Is there a simpler way to write this? Maybe with setoids?}

> restricted_excluded_middle_eq : (n, m : Nat) -> (n = m) `Either` Not (n = m)
> restricted_excluded_middle_eq n m = restricted_excluded_middle (to n m, fro n m)
> where 
>   to : (n, m : Nat) -> (n=m) -> (n==m)=True
>   to Z Z prf = Refl
>   to Z (S _) Refl impossible
>   to (S _) Z Refl impossible
>   to (S k) (S j) prf = to k j (succInjective k j prf)
>   fro : (n, m : Nat) -> (n==m)=True -> (n=m)
>   fro Z Z Refl = Refl
>   fro Z (S _) Refl impossible
>   fro (S _) Z Refl impossible
>   fro (S k) (S j) prf = rewrite fro k j prf in Refl

(Idris has a built-in version of this, called \idr{decEq}.)

It may seem strange that the general excluded middle is not available by default
in Idris; after all, any given claim must be either true or false. Nonetheless,
there is an advantage in not assuming the excluded middle: statements in Idris
can make stronger claims than the analogous statements in standard mathematics.
Notably, if there is a Idris proof of \idr{(x ** p x)}, it is possible to
explicitly exhibit a value of \idr{x} for which we can prove \idr{p x} -- in
other words, every proof of existence is necessarily _constructive_.

Logics like Idris's, which do not assume the excluded middle, are referred to as
_constructive logics_.

More conventional logical systems such as ZFC, in which the excluded middle does
hold for arbitrary propositions, are referred to as _classical_.

The following example illustrates why assuming the excluded middle may lead to
non-constructive proofs:

_Claim_: There exist irrational numbers `a` and `b` such that `a ^ b` is rational.

_Proof_: It is not difficult to show that `sqrt 2` is irrational. If `sqrt 2 ^
sqrt 2` is rational, it suffices to take `a = b = sqrt 2` and we are done.
Otherwise, `sqrt 2 ^ sqrt 2` is irrational. In this case, we can take `a = sqrt
2 ^ sqrt 2` and `b = sqrt 2`, since `a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2)` = sqrt
2 ^ 2 = 2`. $\square$

Do you see what happened here? We used the excluded middle to consider
separately the cases where `sqrt 2 ^ sqrt 2` is rational and where it is not,
without knowing which one actually holds! Because of that, we wind up knowing
that such `a` and `b` exist but we cannot determine what their actual values are
(at least, using this line of argument).

As useful as constructive logic is, it does have its limitations: There are many
statements that can easily be proven in classical logic but that have much more
complicated constructive proofs, and there are some that are known to have no
constructive proof at all! Fortunately, like functional extensionality, the
excluded middle is known to be compatible with Idris's logic, allowing us to add
it safely as an axiom. However, we will not need to do so in this book: the
results that we cover can be developed entirely within constructive logic at
negligible extra cost.

It takes some practice to understand which proof techniques must be avoided in
constructive reasoning, but arguments by contradiction, in particular, are
infamous for leading to non-constructive proofs. Here's a typical example:
suppose that we want to show that there exists \idr{x} with some property
\idr{p}, i.e., such that \idr{p x}. We start by assuming that our conclusion is
false; that is, \idr{Not (x:a ** p x)}. From this premise, it is not hard to
derive \idr{(x:a) -> Not $ p x}. If we manage to show that this intermediate
fact results in a contradiction, we arrive at an existence proof without ever
exhibiting a value of \idr{x} for which \idr{p x} holds!

The technical flaw here, from a constructive standpoint, is that we claimed to
prove \idr{(x ** p x)} using a proof of `Not $ Not (x ** p x)}. Allowing
ourselves to remove double negations from arbitrary statements is equivalent to
assuming the excluded middle, as shown in one of the exercises below. Thus, this
line of reasoning cannot be encoded in Idris without assuming additional axioms.


==== Exercise: 3 stars (excluded_middle_irrefutable)

The consistency of Idris with the general excluded middle axiom requires
complicated reasoning that cannot be carried out within Idris itself. However,
the following theorem implies that it is always safe to assume a decidability
axiom (i.e., an instance of excluded middle) for any _particular_ type \idr{p}.
Why? Because we cannot prove the negation of such an axiom; if we could, we
would have both \idr{Not (p `Either` Not p)} and \idr{Not $ Not (p `Either` Not
p)}, a contradiction.

> excluded_middle_irrefutable : Not $ Not (p `Either` Not p)
> excluded_middle_irrefutable = ?excluded_middle_irrefutable_rhs

$\square$


==== Exercise: 3 stars, advanced (not_exists_dist)

It is a theorem of classical logic that the following two assertions are equivalent:

```idris
    Not (x:a ** Not p x)
    (x:a) -> p x
```

The \idr{dist_not_exists} theorem above proves one side of this equivalence.
Interestingly, the other direction cannot be proved in constructive logic. Your
job is to show that it is implied by the excluded middle.

\todo[inline]{Use \idr{really_believe_me}?}

 not_exists_dist : excluded_middle -> Not (x ** Not $ P x) -> ((x:a) -> P x)

$\square$


==== Exercise: 5 stars, optional (classical_axioms)

For those who like a challenge, here is an exercise taken from the Coq'Art book
by Bertot and Casteran (p. 123). Each of the following four statements, together
with \idr{excluded_middle}, can be considered as characterizing classical logic.
We can't prove any of them in Idris, but we can consistently add any one of them
as an axiom if we wish to work in classical logic.

Prove that all five propositions (these four plus \idr{excluded_middle}) are
equivalent.

> peirce : ((p -> q) -> p) -> p

> double_negation_elimination : Not $ Not p -> p

> de_morgan_not_and_not : Not (Not p, Not q) -> p `Either` q

> implies_to_or : (p -> q) -> ((Not p) `Either` q)

> -- FILL IN HERE

$\square$
