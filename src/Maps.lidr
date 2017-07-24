= Maps: Total and Partial Maps

Maps (or dictionaries) are ubiquitous data structures both generally and in the
theory of programming languages in particular; we're going to need them in many
places in the coming chapters. They also make a nice case study using ideas
we've seen in previous chapters, including building data structures out of
higher-order functions (from `Basics` and `Poly`) and the use of reflection to
streamline proofs (from `IndProp`).

We'll define two flavors of maps: _total_ maps, which include a "default"
element to be returned when a key being looked up doesn't exist, and _partial_
maps, which return a \idr{Maybe} to indicate success or failure. The latter is
defined in terms of the former, using \idr{Maybe} as the default element.


== The Idris Standard Library

\todo[inline]{Edit}

One small digression before we get to maps.

Unlike the chapters we have seen so far, this one does not Require Import the
chapter before it (and, transitively, all the earlier chapters). Instead, in
this chapter and from now, on we're going to import the definitions and theorems
we need directly from Idris's standard library stuff. You should not notice much
difference, though, because we've been careful to name our own definitions and
theorems the same as their counterparts in the standard library, wherever they
overlap.

Require Import Idris.Arith.Arith.
Require Import Idris.Bool.Bool.
Require Import Idris.Strings.String.
Require Import Idris.Logic.FunctionalExtensionality.

Documentation for the standard library can be found at
http://Idris.inria.fr/library/.

The Search command is a good way to look for theorems involving objects of
specific types. Take a minute now to experiment with it.


== Identifiers

First, we need a type for the keys that we use to index into our maps. For this
purpose, we again use the type \idr{Id} from the `Lists` chapter. To make this
chapter self contained, we repeat its definition here, together with the
equality comparison function for \idr{Id} and its fundamental property.

> data Id : Type where
>   MkId : String -> Id

> beq_id : (x1, x2 : Id) -> Bool
> beq_id (MkId n1) (MkId n2) = decAsBool $ decEq n1 n2

\todo[inline]{Edit}

(The function \idr{decEq} comes from Idris's string library. If you check its
result type, you'll see that it does not actually return a \idr{Bool}, but
rather a type that looks like \idr{Either (x = y) (Not (x = y))}, called a
{Dec}, which can be thought of as an "evidence-carrying boolean." Formally, an
element of \idr{Dec (x=y)} is either a proof that two things are equal or a
proof that they are unequal, together with a tag indicating which. But for
present purposes you can think of it as just a fancy \idr{Bool}.)

> beq_id_refl : (x : Id) -> True = beq_id x x
> beq_id_refl (MkId n) with (decEq n n)
>   beq_id_refl _ | Yes _ = Refl
>   beq_id_refl _ | No contra = absurd $ contra Refl

The following useful property of  \idr{beq_id} follows from an analogous lemma
about strings:

\todo[inline]{Copypasted `<->` for now}

> iff : {p,q : Type} -> Type
> iff {p} {q} = (p -> q, q -> p)

> syntax [p] "<->" [q] = iff {p} {q}

> bto : (beq_id x y = True) -> x = y
> bto {x=MkId n1} {y=MkId n2} prf with (decEq n1 n2)
>   bto Refl | (Yes eq) = cong {f=MkId} eq
>   bto prf | (No _) = absurd prf
> bfro : (x = y) -> beq_id x y = True
> bfro {x=MkId n1} {y=MkId n2} prf with (decEq n1 n2)
>   bfro _ | (Yes _) = Refl
>   bfro prf | (No contra) = absurd $ contra $ idInj prf
>   where 
>     idInj : MkId x = MkId y -> x = y  
>     idInj Refl = Refl

> beq_id_true_iff : (beq_id x y = True) <-> x = y
> beq_id_true_iff = (bto, bfro)

Similarly:

\todo[inline]{Copypasted here for now}

> not_true_and_false : (b = False) -> (b = True) -> Void
> not_true_and_false {b=False} _ Refl impossible
> not_true_and_false {b=True} Refl _ impossible
> not_true_is_false : Not (b = True) -> b = False
> not_true_is_false {b=False} h = Refl
> not_true_is_false {b=True} h = absurd $ h Refl

> beq_id_false_iff : (beq_id x y = False) <-> Not (x = y)
> beq_id_false_iff = (to, fro)
> where
>   to : (beq_id x y = False) -> Not (x = y)
>   to beqf = not_true_and_false beqf . bfro 
>   fro : (Not (x = y)) -> beq_id x y = False
>   fro noteq = not_true_is_false $ noteq . bto 


== Total Maps

Our main job in this chapter will be to build a definition of partial maps that
is similar in behavior to the one we saw in the `Lists` chapter, plus
accompanying lemmas about its behavior.

This time around, though, we're going to use _functions_, rather than lists of
key-value pairs, to build maps. The advantage of this representation is that it
offers a more _extensional_ view of maps, where two maps that respond to queries
in the same way will be represented as literally the same thing (the very same
function), rather than just "equivalent" data structures. This, in turn,
simplifies proofs that use maps.

We build partial maps in two steps. First, we define a type of _total maps_ that
return a default value when we look up a key that is not present in the map.

> total_map : Type -> Type 
> total_map a = Id -> a

Intuitively, a total map over an element type \idr{a} is just a function that
can be used to look up \idr{Id}s, yielding \idr{a}s.

The function \idr{t_empty} yields an empty total map, given a default element;
this map always returns the default element when applied to any id.

> t_empty : (v : a) -> total_map a
> t_empty v = \_ => v

More interesting is the \idr{update} function, which (as before) takes a map
\idr{m}, a key \idr{x}, and a value \idr{v} and returns a new map that takes
\idr{x} to \idr{v} and takes every other key to whatever \idr{m} does.

> t_update : (x : Id) -> (v : a) -> (m : total_map a) -> total_map a
> t_update x v m = \x' => if beq_id x x' then v else m x'

This definition is a nice example of higher-order programming: \idr{t_update}
takes a _function_ \idr{m} and yields a new function \idr{\x' => ...} that
behaves like the desired map.

For example, we can build a map taking \idr{Id}s to \idr{Bool}s, where \idr{Id
3} is mapped to \idr{True} and every other key is mapped to \idr{False}, like
this:

\todo[inline]{Seems like an inconsistency in the book here}

> examplemap : total_map Bool
> examplemap = t_update (MkId "foo") False $ 
>              t_update (MkId "bar") True $ 
>              t_empty False

This completes the definition of total maps. Note that we don't need to define a
\idr{find} operation because it is just function application!

> update_example1 : examplemap (MkId "baz") = False
> update_example1 = Refl

> update_example2 : examplemap (MkId "foo") = False
> update_example2 = Refl

> update_example3 : examplemap (MkId "quux") = False
> update_example3 = Refl

> update_example4 : examplemap (MkId "bar") = True
> update_example4 = Refl

To use maps in later chapters, we'll need several fundamental facts about how
they behave. Even if you don't work the following exercises, make sure you
thoroughly understand the statements of the lemmas! (Some of the proofs require
the functional extensionality axiom, which is discussed in the `Logic` chapter.)


==== Exercise: 1 star, optional (t_apply_empty)

First, the empty map returns its default element for all keys:

> t_apply_empty: t_empty v x = v
> t_apply_empty = ?t_apply_empty_rhs

$\square$


==== Exercise: 2 stars, optional (t_update_eq)

Next, if we update a map \idr{m} at a key \idr{x} with a new value v and then
look up x in the map resulting from the update, we get back v:

Lemma t_update_eq : ∀A (m: total_map A) x v,
  (t_update m x v) x = v.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$


==== Exercise: 2 stars, optional (t_update_neq)

On the other hand, if we update a map m at a key x1 and then look up a different
key x2 in the resulting map, we get the same result that m would have given:

Theorem t_update_neq : ∀(X:Type) v x1 x2
                         (m : total_map X),
  x1 ≠ x2 →
  (t_update m x1 v) x2 = m x2.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$


==== Exercise: 2 stars, optional (t_update_shadow)

If we update a map m at a key x with a value v1 and then update again with the
same key x and another value v2, the resulting map behaves the same (gives the
same result when applied to any key) as the simpler map obtained by performing
just the second update on m:

Lemma t_update_shadow : ∀A (m: total_map A) v1 v2 x,
    t_update (t_update m x v1) x v2
  = t_update m x v2.
Proof.
  (* FILL IN HERE *) Admitted.

$\square$

For the final two lemmas about total maps, it's convenient to use the reflection
idioms introduced in chapter IndProp. We begin by proving a fundamental
reflection lemma relating the equality proposition on ids with the boolean
function beq_id.


==== Exercise: 2 stars, optional (beq_idP)

Use the proof of beq_natP in chapter IndProp as a template to prove the following:

Lemma beq_idP : ∀x y, reflect (x = y) (beq_id x y).
Proof.
  (* FILL IN HERE *) Admitted.

$\square$

Now, given ids x1 and x2, we can use the destruct (beq_idP x1 x2) to
simultaneously perform case analysis on the result of beq_id x1 x2 and generate
hypotheses about the equality (in the sense of =) of x1 and x2.


==== Exercise: 2 stars (t_update_same)

With the example in chapter IndProp as a template, use beq_idP to prove the
following theorem, which states that if we update a map to assign key x the same
value as it already has in m, then the result is equal to m:

Theorem t_update_same : ∀X x (m : total_map X),
  t_update m x (m x) = m.
Proof.
  (* FILL IN HERE *) Admitted.

$\square$


==== Exercise: 3 stars, recommended (t_update_permute)

Use beq_idP to prove one final property of the update function: If we update a
map m at two distinct keys, it doesn't matter in which order we do the updates.

Theorem t_update_permute : ∀(X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 ≠ x1 →
    (t_update (t_update m x2 v2) x1 v1)
  = (t_update (t_update m x1 v1) x2 v2).
Proof.
  (* FILL IN HERE *) Admitted.

$\square$

== Partial maps

Finally, we define partial maps on top of total maps. A partial map with
elements of type A is simply a total map with elements of type option A and
default element None.

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Definition update {A:Type} (m : partial_map A)
                  (x : id) (v : A) :=
  t_update m x (Some v).

We now straightforwardly lift all of the basic lemmas about total maps to
partial maps.

Lemma apply_empty : ∀A x, @empty A x = None.

Lemma update_eq : ∀A (m: partial_map A) x v,
  (update m x v) x = Some v.

Theorem update_neq : ∀(X:Type) v x1 x2
                       (m : partial_map X),
  x2 ≠ x1 →
  (update m x2 v) x1 = m x1.

Lemma update_shadow : ∀A (m: partial_map A) v1 v2 x,
  update (update m x v1) x v2 = update m x v2.

Theorem update_same : ∀X v x (m : partial_map X),
  m x = Some v →
  update m x v = m.

Theorem update_permute : ∀(X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 ≠ x1 →
    (update (update m x2 v2) x1 v1)
  = (update (update m x1 v1) x2 v2).
