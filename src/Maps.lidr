= Maps: Total and Partial Maps

> module Maps
>

Maps (or dictionaries) are ubiquitous data structures both generally and in the
theory of programming languages in particular; we're going to need them in many
places in the coming chapters. They also make a nice case study using ideas
we've seen in previous chapters, including building data structures out of
higher-order functions (from `Basics` and `Poly`) and the use of reflection to
streamline proofs (from `IndProp`).

We'll define two flavors of maps: _total_ maps, which include a "default"
element to be returned when a key being looked up doesn't exist, and _partial_
maps, which return a \idr{Maybe} to indicate success or failure. The latter is
defined in terms of the former, using \idr{Nothing} as the default element.


== The Idris Standard Library

\todo[inline]{Edit}

One small digression before we get to maps.

Unlike the chapters we have seen so far, this one does not `Require Import` the
chapter before it (and, transitively, all the earlier chapters). Instead, in
this chapter and from now, on we're going to import the definitions and theorems
we need directly from Idris's standard library stuff. You should not notice much
difference, though, because we've been careful to name our own definitions and
theorems the same as their counterparts in the standard library, wherever they
overlap.

```coq
Require Import Idris.Arith.Arith.
Require Import Idris.Bool.Bool.
Require Import Idris.Strings.String.
Require Import Idris.Logic.FunctionalExtensionality.
```

Documentation for the standard library can be found at
\url{https://www.idris-lang.org/docs/current/}.

The \idr{:search} command is a good way to look for theorems involving objects
of specific types. Take a minute now to experiment with it.


== Identifiers

First, we need a type for the keys that we use to index into our maps. For this
purpose, we again use the type \idr{Id} from the `Lists` chapter. To make this
chapter self contained, we repeat its definition here, together with the
equality comparison function for \idr{Id} and its fundamental property.

> data Id : Type where
>   MkId : String -> Id
>
> beq_id : (x1, x2 : Id) -> Bool
> beq_id (MkId n1) (MkId n2) = decAsBool $ decEq n1 n2
>

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
>   beq_id_refl _ | Yes _     = Refl
>   beq_id_refl _ | No contra = absurd $ contra Refl
>

The following useful property of  \idr{beq_id} follows from an analogous lemma
about strings:

\todo[inline]{Copied \idr{<->} for now}

> iff : {p,q : Type} -> Type
> iff {p} {q} = (p -> q, q -> p)
>
> syntax [p] "<->" [q] = iff {p} {q}
>

\todo[inline]{Remove when a release with
https://github.com/idris-lang/Idris-dev/pull/3925 happens}

> Uninhabited (False = True) where
>   uninhabited Refl impossible
>

> beq_id_true_iff : (beq_id x y = True) <-> x = y
> beq_id_true_iff = (bto, bfro)
>   where
>     bto : (beq_id x y = True) -> x = y
>     bto {x=MkId n1} {y=MkId n2} prf with (decEq n1 n2)
>       bto Refl | Yes eq = cong {f=MkId} eq
>       bto prf  | No _   = absurd prf
>
>     idInj : MkId x = MkId y -> x = y
>     idInj Refl = Refl
>
>     bfro : (x = y) -> beq_id x y = True
>     bfro {x=MkId n1} {y=MkId n2} prf with (decEq n1 n2)
>       bfro _   | Yes _     = Refl
>       bfro prf | No contra = absurd $ contra $ idInj prf
>

Similarly:

\todo[inline]{Copied and inlined \idr{not_true_iff_false} from \idr{Logic} here
for now}

> not_true_and_false : (b = False) -> Not (b = True)
> not_true_and_false {b=False} _ Refl impossible
> not_true_and_false {b=True} Refl _ impossible
>
> not_true_is_false : Not (b = True) -> b = False
> not_true_is_false {b=False} h = Refl
> not_true_is_false {b=True} h  = absurd $ h Refl
>
> beq_id_false_iff : (beq_id x y = False) <-> Not (x = y)
> beq_id_false_iff = (to, fro)
>   where
>     to : (beq_id x y = False) -> Not (x = y)
>     to beqf = not_true_and_false beqf . (snd beq_id_true_iff)
>
>     fro : (Not (x = y)) -> beq_id x y = False
>     fro noteq = not_true_is_false $ noteq . (fst beq_id_true_iff)
>


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
>

Intuitively, a total map over an element type \idr{a} is just a function that
can be used to look up \idr{Id}s, yielding \idr{a}s.

The function \idr{t_empty} yields an empty total map, given a default element;
this map always returns the default element when applied to any id.

> t_empty : (v : a) -> total_map a
> t_empty v = \_ => v
>

We can also write this as:

```idris
t_empty = const
```

More interesting is the \idr{update} function, which (as before) takes a map
\idr{m}, a key \idr{x}, and a value \idr{v} and returns a new map that takes
\idr{x} to \idr{v} and takes every other key to whatever \idr{m} does.

> t_update : (x : Id) -> (v : a) -> (m : total_map a) -> total_map a
> t_update x v m = \x' => if beq_id x x' then v else m x'
>

This definition is a nice example of higher-order programming: \idr{t_update}
takes a _function_ \idr{m} and yields a new function \idr{\x' => ...} that
behaves like the desired map.

For example, we can build a map taking \idr{Id}s to \idr{Bool}s, where \idr{Id
3} is mapped to \idr{True} and every other key is mapped to \idr{False}, like
this:

\todo[inline]{Seems like a wrong description in the book here}

> examplemap : total_map Bool
> examplemap = t_update (MkId "foo") False $
>              t_update (MkId "bar") True $
>              t_empty False
>

This completes the definition of total maps. Note that we don't need to define a
\idr{find} operation because it is just function application!

> update_example1 : examplemap (MkId "baz") = False
> update_example1 = Refl
>
> update_example2 : examplemap (MkId "foo") = False
> update_example2 = Refl
>
> update_example3 : examplemap (MkId "quux") = False
> update_example3 = Refl
>
> update_example4 : examplemap (MkId "bar") = True
> update_example4 = Refl
>

To use maps in later chapters, we'll need several fundamental facts about how
they behave. Even if you don't work the following exercises, make sure you
thoroughly understand the statements of the lemmas! (Some of the proofs require
the functional extensionality axiom, which is discussed in the `Logic` chapter.)


==== Exercise: 1 star, optional (t_apply_empty)

First, the empty map returns its default element for all keys:

> t_apply_empty : t_empty v x = v
> t_apply_empty = ?t_apply_empty_rhs
>

$\square$


==== Exercise: 2 stars, optional (t_update_eq)

Next, if we update a map \idr{m} at a key \idr{x} with a new value \idr{v} and
then look up \idr{x} in the map resulting from the \idr{update}, we get back
\idr{v}:

> t_update_eq : (t_update x v m) x = v
> t_update_eq = ?t_update_eq_rhs
>

$\square$


==== Exercise: 2 stars, optional (t_update_neq)

On the other hand, if we update a map \idr{m} at a key \idr{x1} and then look up
a _different_ key \idr{x2} in the resulting map, we get the same result that
\idr{m} would have given:

> t_update_neq : Not (x1 = x2) -> (t_update x1 v m) x2 = m x2
> t_update_neq neq = ?t_update_neq_rhs
>

$\square$


==== Exercise: 2 stars, optional (t_update_shadow)

If we update a map \idr{m} at a key \idr{x} with a value \idr{v1} and then
update again with the same key \idr{x} and another value \idr{v2}, the resulting
map behaves the same (gives the same result when applied to any key) as the
simpler map obtained by performing just the second \idr{update} on \idr{m}:

> t_update_shadow : t_update x v2 $ t_update x v1 m = t_update x v2 m
> t_update_shadow = ?t_update_shadow_rhs
>

$\square$

For the final two lemmas about total maps, it's convenient to use the reflection
idioms introduced in chapter `IndProp`. We begin by proving a fundamental
_reflection lemma_ relating the equality proposition on \idr{Id}s with the
boolean function \idr{beq_id}.


==== Exercise: 2 stars, optional (beq_idP)

Use the proof of \idr{beq_natP} in chapter `IndProp` as a template to prove the
following:

\todo[inline]{Copied \idr{Reflect} for now}

> data Reflect : Type -> Bool -> Type where
>   ReflectT : (p : Type) -> Reflect p True
>   ReflectF : (p : Type) -> (Not p) -> Reflect p False
>
> beq_idP : Reflect (x = y) (beq_id x y)
> beq_idP = ?beq_idP_rhs
>

$\square$

Now, given \idr{Id}s \idr{x1} and \idr{x2}, we can use \idr{with (beq_idP x1
x2)} to simultaneously perform case analysis on the result of \idr{beq_id x1 x2}
and generate hypotheses about the equality (in the sense of \idr{=}) of \idr{x1}
and \idr{x2}.


==== Exercise: 2 stars (t_update_same)

With the example in chapter `IndProp` as a template, use \idr{beq_idP} to prove
the following theorem, which states that if we update a map to assign key
\idr{x} the same value as it already has in \idr{m}, then the result is equal to
\idr{m}:

> t_update_same : t_update x (m x) m = m
> t_update_same = ?t_update_same_rhs
>

$\square$


==== Exercise: 3 stars, recommended (t_update_permute)

Use \idr{beq_idP} to prove one final property of the \idr{update} function: If
we update a map \idr{m} at two distinct keys, it doesn't matter in which order
we do the updates.

> t_update_permute : Not (x2 = x1) -> t_update x1 v1 $ t_update x2 v2 m
>                                   = t_update x2 v2 $ t_update x1 v1 m
> t_update_permute neq = ?t_update_permute_rhs
>

$\square$


== Partial maps

Finally, we define _partial maps_ on top of total maps. A partial map with
elements of type \idr{a} is simply a total map with elements of type \idr{Maybe
a} and default element \idr{Nothing}.

> partial_map : Type -> Type
> partial_map a = total_map (Maybe a)
>
> empty : partial_map a
> empty = t_empty Nothing
>
> update : (x : Id) -> (v : a) -> (m : partial_map a) -> partial_map a
> update x v m = t_update x (Just v) m
>

We now straightforwardly lift all of the basic lemmas about total maps to
partial maps.

> apply_empty : empty {a} x = Nothing {a}
> apply_empty = Refl
>
> update_eq : (update x v m) x = Just v
> update_eq {x} {v} {m} =
>   rewrite t_update_eq {x} {v=Just v} {m} in
>           Refl
>
> update_neq : Not (x2 = x1) -> (update x2 v m) x1 = m x1
> update_neq {x1} {x2} {v} {m} neq =
>   rewrite t_update_neq neq {x1=x2} {x2=x1} {v=Just v} {m} in
>           Refl
>
> update_shadow : update x v2 $ update x v1 m = update x v2 m
> update_shadow {x} {v1} {v2} {m} =
>   rewrite t_update_shadow {x} {v1=Just v1} {v2=Just v2} {m} in
>           Refl
>
> update_same : m x = Just v -> update x v m = m
> update_same {x} {m} prf =
>   rewrite sym prf in
>   rewrite t_update_same {x} {m} in
>           Refl
>
> update_permute : Not (x2 = x1) -> update x1 v1 $ update x2 v2 m
>                                 = update x2 v2 $ update x1 v1 m
> update_permute {v1} {v2} {m} neq =
>   rewrite t_update_permute neq {v1=Just v1} {v2=Just v2} {m} in
>           Refl
