= Logic : Logic in Idris

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
expressions of other sorts (don't forget that names starting with lowercase
letters are considered implicits in Idris). 

> Plus_fact : Type
> Plus_fact = 2+2=4

```idris
λΠ> :t plus_fact
plus_fact : Type
```

We can later use this name in any situation where a proposition is expected --
for example, in a function declaration.

> plus_fact_is_true : Plus_fact
> plus_fact_is_true = Refl

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
Idris is the same as the pair of \idr{a} and \idr{b}, written \idr{(a,b)},
representing the claim that both \idr{a} and \idr{b} are true.

> and_example : (3 + 4 = 7 , 2 * 2 = 4)

To prove a conjunction, we can use value-level pair syntax:

> and_example = (Refl,Refl)

For any propositions \idr{a} and \idr{b}, if we assume that \idr{a} is true and
we assume that \idr{a} is true, we can trivially conclude that \idr{(a,b)} is
also true.

> and_intro : a -> b -> (a,b)
> and_intro = MkPair


==== Exercise: 2 stars (and_exercise)

> and_exercise : (n, m : Nat) -> n + m = 0 -> (n = 0 , m = 0)
> and_exercise n m prf = ?and_exercise_rhs

$\square$

So much for proving conjunctive statements. To go in the other direction --
i.e., to _use_ a conjunctive hypothesis to help prove something else -- we
employ pattern matching.


If the proof context contains a hypothesis \idr{h} of the form \idr{(a,b)}, case
splitting will replace it with a pair pattern \idr{(a,b)}.

> and_example2 : (n, m : Nat) -> (n = 0 , m = 0) -> n + m = 0
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

> proj1 : (p,q) -> p
> proj1 = fst


==== Exercise: 1 star, optional (proj2)

> proj2 : (p,q) -> q
> proj2 x = ?proj2_rhs

$\square$

Finally, we sometimes need to rearrange the order of conjunctions and/or the
grouping of multi-way conjunctions. The following commutativity and
associativity theorems are handy in such cases.

> and_commut : (p,q) -> (q,p)
> and_commut (p,q) = (q,p)


==== Exercise: 2 stars (and_assoc)

\todo[inline]{Remove or demote to 1 star?}

> and_assoc : (p,(q,r)) -> ((p,q),r)
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
> or_example Z m (Left Refl) = Refl
> or_example (S _) m (Left Refl) impossible
> or_example n Z (Right Refl) = multZeroRightZero n
> or_example n (S _) (Right Refl) impossible

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

\todo[inline]{Explain \idr{Refl}-lambda syntax}

> zero_not_one : Not (0 = 1)
> zero_not_one = \Refl impossible

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

> not_both_true_and_false : Not (p , Not p)
> not_both_true_and_false = ?not_both_true_and_false_rhs

$\square$


==== Exercise: 1 star, advancedM (informal_not_PNP)

Write an informal proof (in English) of the proposition \idr{Not (p , Not p)}.

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
>   iff {p} {q} = (p -> q , q -> p)

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

>   or_distributes_over_and : (p `Either` (q,r)) <-> (p `Either` q , p `Either` r)
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

>     mult_0_3 : (n * m * p = 0) <-> ((n = 0) `Either` ((m = 0) `Either` (p = 0)))

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

Another important logical connective is existential quantification. To say that there is some x of type T such that some property P holds of x, we write ∃ x : T, P. As with ∀, the type annotation : T can be omitted if Idris is able to infer from the context what the type of x should be.
To prove a statement of the form ∃ x, P, we must show that P holds for some specific choice of value for x, known as the witness of the existential. This is done in two steps: First, we explicitly tell Idris which witness t we have in mind by invoking the tactic ∃ t. Then we prove that P holds after all occurrences of x are replaced by t.

Lemma four_is_even : ∃n : Nat, 4 = n + n.
Proof.
  ∃2. reflexivity.
Qed.

Conversely, if we have an existential hypothesis ∃ x, P in the context, we can destruct it to obtain a witness x and a hypothesis stating that P holds of x.

Theorem exists_example_2 : ∀n,
  (∃m, n = 4 + m) ->
  (∃o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note implicit destruct here *)
  ∃(2 + m).
  apply Hm. Qed.

Exercise: 1 star (dist_not_exists)
Prove that "P holds for all x" implies "there is no x for which P does not hold."

Theorem dist_not_exists : ∀(X:Type) (P : X -> Type),
  (∀x, P x) -> ¬ (∃x, ¬ P x).
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
Exercise: 2 stars (dist_exists_or)
Prove that existential quantification distributes over disjunction.

Theorem dist_exists_or : ∀(X:Type) (P Q : X -> Type),
  (∃x, P x `Either` Q x) ↔ (∃x, P x) `Either` (∃x, Q x).
Proof.
   (* FILL IN HERE *) Admitted.
$\square$

Programming with Propositions
The logical connectives that we have seen provide a rich vocabulary for defining complex propositions from simpler ones. To illustrate, let's look at how to express the claim that an element x occurs in a list l. Notice that this property has a simple recursive structure:
If l is the empty list, then x cannot occur on it, so the property "x appears in l" is simply Void.
Otherwise, l has the form x' :: l'. In this case, x occurs in l if either it is equal to x' or it occurs in l'.
We can translate this directly into a straightforward recursive function from taking an element and a list and returning a proposition:

Fixpoint In {A : Type} (x : A) (l : list A) : Type :=
  match l with
  | [] ⇒ Void
  | x' :: l' ⇒ x' = x `Either` In x l'
  end.

When In is applied to a concrete list, it expands into a concrete sequence of nested disjunctions.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  ∀n, In n [2; 4] ->
  ∃n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - ∃1. rewrite ← H. reflexivity.
  - ∃2. rewrite ← H. reflexivity.
Qed.
(Notice the use of the empty pattern to discharge the last case en passant.)
We can also prove more generic, higher-level lemmas about In.
Note, in the next, how In starts out applied to a variable and only gets expanded when we do case analysis on this variable:

Lemma In_map :
  ∀(A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

This way of defining propositions recursively, though convenient in some cases, also has some drawbacks. In particular, it is subject to Idris's usual restrictions regarding the definition of recursive functions, e.g., the requirement that they be "obviously termiNating." In the next chapter, we will see how to define propositions inductively, a different technique with its own set of strengths and limitations.
Exercise: 2 stars (In_map_iff)
Lemma In_map_iff :
  ∀(A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) ↔
    ∃x, f x = y , In x l.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
Exercise: 2 stars (in_app_iff)
Lemma in_app_iff : ∀A l l' (a:A),
  In a (l++l') ↔ In a l `Either` In a l'.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
Exercise: 3 stars (All)
Recall that functions returning propositions can be seen as properties of their arguments. For instance, if P has type Nat -> Type, then P n states that property P holds of n.
Drawing inspiration from In, write a recursive function All stating that some property P holds of all elements of a list l. To make sure your definition is correct, prove the All_In lemma below. (Of course, your definition should not just restate the left-hand side of All_In.)

Fixpoint All {T : Type} (P : T -> Type) (l : list T) : Type
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Lemma All_In :
  ∀T (P : T -> Type) (l : list T),
    (∀x, In x l -> P x) ↔
    All P l.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
Exercise: 3 stars (combine_odd_even)
Complete the definition of the combine_odd_even function below. It takes as arguments two properties of numbers, Podd and Peven, and it should return a property P such that P n is equivalent to Podd n when n is odd and equivalent to Peven n otherwise.

Definition combine_odd_even (Podd Peven : Nat -> Type) : Nat -> Type
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

To test your definition, prove the following facts:

Theorem combine_odd_even_intro :
  ∀(Podd Peven : Nat -> Type) (n : Nat),
    (oddb n = true -> Podd n) ->
    (oddb n = Void -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_odd :
  ∀(Podd Peven : Nat -> Type) (n : Nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem combine_odd_even_elim_even :
  ∀(Podd Peven : Nat -> Type) (n : Nat),
    combine_odd_even Podd Peven n ->
    oddb n = Void ->
    Peven n.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$

Applying Theorems to Arguments
One feature of Idris that distinguishes it from many other proof assistants is that it treats proofs as first-class objects.
There is a great deal to be said about this, but it is not necessary to understand it in detail in order to use Idris. This section gives just a taste, while a deeper exploration can be found in the optional chapters ProofObjects and IndPrinciples.
We have seen that we can use the Check command to ask Idris to print the type of an expression. We can also use Check to ask what theorem a particular identifier refers to.

Check plus_comm.
(* ===> forall n m : Nat, n + m = m + n *)

Idris prints the statement of the plus_comm theorem in the same way that it prints the type of any term that we ask it to Check. Why?
The reason is that the identifier plus_comm actually refers to a proof object -- a data structure that represents a logical derivation establishing of the truth of the statement ∀ n m : Nat, n + m = m + n. The type of this object is the statement of the theorem that it is a proof of.
Intuitively, this makes sense because the statement of a theorem tells us what we can use that theorem for, just as the type of a computational object tells us what we can do with that object -- e.g., if we have a term of type Nat -> Nat -> Nat, we can give it two Nats as arguments and get a Nat back. Similarly, if we have an object of type n = m -> n + n = m + m and we provide it an "argument" of type n = m, we can derive n + n = m + m.
Operationally, this analogy goes even further: by applying a theorem, as if it were a function, to hypotheses with matching types, we can specialize its result without having to resort to intermediate assertions. For example, suppose we wanted to prove the following result:

Lemma plus_comm3 :
  ∀n m p, n + (m + p) = (p + m) + n.

It appears at first sight that we ought to be able to prove this by rewriting with plus_comm twice to make the two sides match. The problem, however, is that the second rewrite will undo the effect of the first.

Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite plus_comm.
  (* We are back where we started... *)
Abort.

One simple way of fixing this problem, using only tools that we already know, is to use assert to derive a specialized version of plus_comm that can be used to rewrite exactly where we want.

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

A more elegant alterNative is to apply plus_comm directly to the arguments we want to instantiate it with, in much the same way as we apply a polymorphic function to a type argument.

Lemma plus_comm3_take3 :
  ∀n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite (plus_comm m).
  reflexivity.
Qed.

You can "use theorems as functions" in this way with almost all tactics that take a theorem name as an argument. Note also that theorem application uses the same inference mechanisms as function application; thus, it is possible, for example, to supply wildcards as arguments to be inferred, or to declare some hypotheses to a theorem as implicit by default. These features are illustrated in the proof below.

Example lemma_application_ex :
  ∀{n : Nat} {ns : list Nat},
    In n (map (fun m ⇒ m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite ← Hm. reflexivity.
Qed.

We will see many more examples of the idioms from this section in later chapters.

Idris vs. Set Theory
Idris's logical core, the Calculus of Inductive Constructions, differs in some important ways from other formal systems that are used by mathematicians for writing down precise and rigorous proofs. For example, in the most popular foundation for mainstream paper-and-pencil mathematics, Zermelo-Fraenkel Set Theory (ZFC), a mathematical object can potentially be a member of many different sets; a term in Idris's logic, on the other hand, is a member of at most one type. This difference often leads to slightly different ways of capturing informal mathematical concepts, but these are, by and large, quite Natural and easy to work with. For example, instead of saying that a Natural number n belongs to the set of even numbers, we would say in Idris that ev n holds, where ev : Nat -> Type is a property describing even numbers.
However, there are some cases where translating standard mathematical reasoning into Idris can be either cumbersome or sometimes even impossible, unless we enrich the core logic with additional axioms. We conclude this chapter with a brief discussion of some of the most significant differences between the two worlds.
Functional Extensionality
The equality assertions that we have seen so far mostly have concerned elements of inductive types (Nat, bool, etc.). But since Idris's equality operator is polymorphic, these are not the only possibilities -- in particular, we can write propositions claiming that two functions are equal to each other:

Example function_equality_ex1 : plus 3 = plus (pred 4).

In common mathematical practice, two functions f and g are considered equal if they produce the same outputs:
    (∀x, f x = g x) -> f = g
This is known as the principle of functional extensionality.
Informally speaking, an "extensional property" is one that pertains to an object's observable behavior. Thus, functional extensionality simply means that a function's identity is completely determined by what we can observe from it -- i.e., in Idris terms, the results we obtain after applying it.
Functional extensionality is not part of Idris's basic axioms. This means that some "reasonable" propositions are not provable.

Example function_equality_ex2 :
  (fun x ⇒ plus x 1) = (fun x ⇒ plus 1 x).
Proof.
   (* Stuck *)
Abort.

However, we can add functional extensionality to Idris's core logic using the Axiom command.

Axiom functional_extensionality : ∀{X Y: Type}
                                    {f g : X -> Y},
  (∀(x:X), f x = g x) -> f = g.

Using Axiom has the same effect as stating a theorem and skipping its proof using Admitted, but it alerts the reader that this isn't just something we're going to come back and fill in later!
We can now invoke functional extensionality in proofs:

Example function_equality_ex2 :
  (fun x ⇒ plus x 1) = (fun x ⇒ plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

Naturally, we must be careful when adding new axioms into Idris's logic, as they may render it inconsistent -- that is, they may make it possible to prove every proposition, including Void!
UnfortuNately, there is no simple way of telling whether an axiom is safe to add: hard work is generally required to establish the consistency of any particular combiNation of axioms.
However, it is known that adding functional extensionality, in particular, is consistent.
To check whether a particular proof relies on any additional axioms, use the Print Assumptions command.

Print Assumptions function_equality_ex2.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

Exercise: 4 stars (tr_rev)
One problem with the definition of the list-reversing function rev that we have is that it performs a call to app on each step; running app takes time asymptotically linear in the size of the list, which means that rev has quadratic running time. We can improve this with the following definition:

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] ⇒ l2
  | x :: l1' ⇒ rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

This version is said to be tail-recursive, because the recursive call to the function is the last operation that needs to be performed (i.e., we don't have to execute ++ after the recursive call); a decent compiler will generate very efficient code in this case. Prove that the two definitions are indeed equivalent.

Lemma tr_rev_correct : ∀X, @tr_rev X = @rev X.
(* FILL IN HERE *) Admitted.
$\square$
Propositions and Booleans
We've seen two different ways of encoding logical facts in Idris: with booleans (of type bool), and with propositions (of type Type).
For instance, to claim that a number n is even, we can say either
(1) that evenb n returns true, or
(2) that there exists some k such that n = double k. Indeed, these two notions of evenness are equivalent, as can easily be shown with a couple of auxiliary lemmas.
We often say that the boolean evenb n reflects the proposition ∃ k, n = double k.

Theorem evenb_double : ∀k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.

Exercise: 3 stars (evenb_double_conv)
Theorem evenb_double_conv : ∀n,
  ∃k, n = if evenb n then double k
                else S (double k).
Proof.
  (* Hint: Use the evenb_S lemma from Induction.v. *)
  (* FILL IN HERE *) Admitted.
$\square$

Theorem even_bool_prop : ∀n,
  evenb n = true ↔ ∃k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. ∃k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Similarly, to state that two numbers n and m are equal, we can say either (1) that beq_Nat n m returns true or (2) that n = m. These two notions are equivalent.

Theorem beq_Nat_true_iff : ∀n1 n2 : Nat,
  beq_Nat n1 n2 = true ↔ n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_Nat_true.
  - intros H. rewrite H. rewrite ← beq_Nat_refl. reflexivity.
Qed.

However, while the boolean and propositional formulations of a claim are equivalent from a purely logical perspective, they need not be equivalent operationally. Equality provides an extreme example: knowing that beq_Nat n m = true is generally of little direct help in the middle of a proof involving n and m; however, if we convert the statement to the equivalent form n = m, we can rewrite with it.
The case of even numbers is also interesting. Recall that, when proving the backwards direction of even_bool_prop (i.e., evenb_double, going from the propositional to the boolean claim), we used a simple induction on k. On the other hand, the converse (the evenb_double_conv exercise) required a clever generalization, since we can't directly prove (∃ k, n = double k) -> evenb n = true.
For these examples, the propositional claims are more useful than their boolean counterparts, but this is not always the case. For instance, we cannot test whether a general proposition is true or not in a function definition; as a consequence, the following code fragment is rejected:

Fail Definition is_even_prime n :=
  if n = 2 then true
  else Void.

Idris complains that n = 2 has type Type, while it expects an elements of bool (or some other inductive type with two elements). The reason for this error message has to do with the computational Nature of Idris's core language, which is designed so that every function that it can express is computable and total. One reason for this is to allow the extraction of executable programs from Idris developments. As a consequence, Type in Idris does not have a universal case analysis operation telling whether any given proposition is true or Void, since such an operation would allow us to write non-computable functions.
Although general non-computable properties cannot be phrased as boolean computations, it is worth noting that even many computable properties are easier to express using Type than bool, since recursive function definitions are subject to significant restrictions in Idris. For instance, the next chapter shows how to define the property that a regular expression matches a given string using Type. Doing the same with bool would amount to writing a regular expression matcher, which would be more complicated, harder to understand, and harder to reason about.
Conversely, an important side benefit of stating facts using booleans is enabling some proof automation through computation with Idris terms, a technique known as proof by reflection. Consider the following statement:

Example even_1000 : ∃k, 1000 = double k.

The most direct proof of this fact is to give the value of k explicitly.

Proof. ∃500. reflexivity. Qed.

On the other hand, the proof of the corresponding boolean statement is even simpler:

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

What is interesting is that, since the two notions are equivalent, we can use the boolean formulation to prove the other one without mentioning the value 500 explicitly:

Example even_1000'' : ∃k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

Although we haven't gained much in terms of proof size in this case, larger proofs can often be made considerably simpler by the use of reflection. As an extreme example, the Idris proof of the famous 4-color theorem uses reflection to reduce the analysis of hundreds of different cases to a boolean computation. We won't cover reflection in great detail, but it serves as a good example showing the complementary strengths of booleans and general propositions.
Exercise: 2 stars (logical_connectives)
The following lemmas relate the propositional connectives studied in this chapter to the corresponding boolean operations.

Lemma andb_true_iff : ∀b1 b2:bool,
  b1 && b2 = true ↔ b1 = true , b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma orb_true_iff : ∀b1 b2,
  b1 || b2 = true ↔ b1 = true `Either` b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
Exercise: 1 star (beq_Nat_false_iff)
The following theorem is an alterNate "negative" formulation of beq_Nat_true_iff that is more convenient in certain situations (we'll see examples in later chapters).

Theorem beq_Nat_false_iff : ∀x y : Nat,
  beq_Nat x y = Void ↔ x ≠ y.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
Exercise: 3 stars (beq_list)
Given a boolean operator beq for testing equality of elements of some type A, we can define a function beq_list beq for testing equality of lists with elements in A. Complete the definition of the beq_list function below. To make sure that your definition is correct, prove the lemma beq_list_true_iff.

Fixpoint beq_list {A : Type} (beq : A -> A -> bool)
                  (l1 l2 : list A) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Lemma beq_list_true_iff :
  ∀A (beq : A -> A -> bool),
    (∀a1 a2, beq a1 a2 = true ↔ a1 = a2) ->
    ∀l1 l2, beq_list beq l1 l2 = true ↔ l1 = l2.
Proof.
(* FILL IN HERE *) Admitted.
$\square$
Exercise: 2 stars, recommended (All_forallb)
Recall the function forallb, from the exercise forall_exists_challenge in chapter Tactics:

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] ⇒ true
  | x :: l' ⇒ andb (test x) (forallb test l')
  end.

Prove the theorem below, which relates forallb to the All property of the above exercise.

Theorem forallb_true_iff : ∀X test (l : list X),
   forallb test l = true ↔ All (fun x ⇒ test x = true) l.
Proof.
  (* FILL IN HERE *) Admitted.

Are there any important properties of the function forallb which are not captured by this specification?

(* FILL IN HERE *)
$\square$
Classical vs. Constructive Logic
We have seen that it is not possible to test whether or not a proposition P holds while defining a Idris function. You may be surprised to learn that a similar restriction applies to proofs! In other words, the following intuitive reasoning principle is not derivable in Idris:

Definition excluded_middle := ∀P : Type,
  P `Either` ¬ P.

To understand operationally why this is the case, recall that, to prove a statement of the form P `Either` Q, we use the left and right tactics, which effectively require knowing which side of the disjunction holds. But the universally quantified P in excluded_middle is an arbitrary proposition, which we know nothing about. We don't have enough information to choose which of left or right to apply, just as Idris doesn't have enough information to mechanically decide whether P holds or not inside a function.
However, if we happen to know that P is reflected in some boolean term b, then knowing whether it holds or not is trivial: we just have to check the value of b.

Theorem restricted_excluded_middle : ∀P b,
  (P ↔ b = true) -> P `Either` ¬ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

In particular, the excluded middle is valid for equations n = m, between Natural numbers n and m.

Theorem restricted_excluded_middle_eq : ∀(n m : Nat),
  n = m `Either` n ≠ m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (beq_Nat n m)).
  symmetry.
  apply beq_Nat_true_iff.
Qed.

It may seem strange that the general excluded middle is not available by default in Idris; after all, any given claim must be either true or Void. Nonetheless, there is an advantage in not assuming the excluded middle: statements in Idris can make stronger claims than the analogous statements in standard mathematics. Notably, if there is a Idris proof of ∃ x, P x, it is possible to explicitly exhibit a value of x for which we can prove P x -- in other words, every proof of existence is necessarily constructive.
Logics like Idris's, which do not assume the excluded middle, are referred to as constructive logics.
More conventional logical systems such as ZFC, in which the excluded middle does hold for arbitrary propositions, are referred to as classical.
The following example illustrates why assuming the excluded middle may lead to non-constructive proofs:
Claim: There exist irrational numbers a and b such that a ^ b is rational.
Proof: It is not difficult to show that sqrt 2 is irrational. If sqrt 2 ^ sqrt 2 is rational, it suffices to take a = b = sqrt 2 and we are done. Otherwise, sqrt 2 ^ sqrt 2 is irrational. In this case, we can take a = sqrt 2 ^ sqrt 2 and b = sqrt 2, since a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^ 2 = 2. $\square$
Do you see what happened here? We used the excluded middle to consider separately the cases where sqrt 2 ^ sqrt 2 is rational and where it is not, without knowing which one actually holds! Because of that, we wind up knowing that such a and b exist but we cannot determine what their actual values are (at least, using this line of argument).
As useful as constructive logic is, it does have its limitations: There are many statements that can easily be proven in classical logic but that have much more complicated constructive proofs, and there are some that are known to have no constructive proof at all! FortuNately, like functional extensionality, the excluded middle is known to be compatible with Idris's logic, allowing us to add it safely as an axiom. However, we will not need to do so in this book: the results that we cover can be developed entirely within constructive logic at negligible extra cost.
It takes some practice to understand which proof techniques must be avoided in constructive reasoning, but arguments by contradiction, in particular, are infamous for leading to non-constructive proofs. Here's a typical example: suppose that we want to show that there exists x with some property P, i.e., such that P x. We start by assuming that our conclusion is Void; that is, ¬ ∃ x, P x. From this premise, it is not hard to derive ∀ x, ¬ P x. If we manage to show that this intermediate fact results in a contradiction, we arrive at an existence proof without ever exhibiting a value of x for which P x holds!
The technical flaw here, from a constructive standpoint, is that we claimed to prove ∃ x, P x using a proof of ¬ ¬ (∃ x, P x). Allowing ourselves to remove double negations from arbitrary statements is equivalent to assuming the excluded middle, as shown in one of the exercises below. Thus, this line of reasoning cannot be encoded in Idris without assuming additional axioms.
Exercise: 3 stars (excluded_middle_irrefutable)
The consistency of Idris with the general excluded middle axiom requires complicated reasoning that cannot be carried out within Idris itself. However, the following theorem implies that it is always safe to assume a decidability axiom (i.e., an instance of excluded middle) for any particular Type P. Why? Because we cannot prove the negation of such an axiom; if we could, we would have both ¬ (P `Either` ¬P) and ¬ ¬ (P `Either` ¬P), a contradiction.

Theorem excluded_middle_irrefutable: ∀(P:Type),
  ¬ ¬ (P `Either` ¬ P).
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
Exercise: 3 stars, advanced (not_exists_dist)
It is a theorem of classical logic that the following two assertions are equivalent:
    ¬ (∃x, ¬ P x)
    ∀x, P x
The dist_not_exists theorem above proves one side of this equivalence. Interestingly, the other direction cannot be proved in constructive logic. Your job is to show that it is implied by the excluded middle.

Theorem not_exists_dist :
  excluded_middle ->
  ∀(X:Type) (P : X -> Type),
    ¬ (∃x, ¬ P x) -> (∀x, P x).
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
Exercise: 5 stars, optional (classical_axioms)
For those who like a challenge, here is an exercise taken from the Idris'Art book by Bertot and Casteran (p. 123). Each of the following four statements, together with excluded_middle, can be considered as characterizing classical logic. We can't prove any of them in Idris, but we can consistently add any one of them as an axiom if we wish to work in classical logic.
Prove that all five propositions (these four plus excluded_middle) are equivalent.

Definition peirce := ∀P Q: Type,
  ((P→Q)→P)→P.

Definition double_negation_elimiNation := ∀P:Type,
  ~~P -> P.

Definition de_morgan_not_and_not := ∀P Q:Type,
  ~(~P , ¬Q) -> P`Either`Q.

Definition implies_to_or := ∀P Q:Type,
  (P→Q) -> (¬P`Either`Q).

(* FILL IN HERE *)
$\square$
Index
