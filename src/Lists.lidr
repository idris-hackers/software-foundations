= Lists: Working with Structured Data

> import Basics

> %hide Prelude.Basics.fst
> %hide Prelude.Basics.snd
> %hide Prelude.Nat.pred

> %default total


== Pairs of Numbers

In an inductive type definition, each constructor can take any number of
arguments -- none (as with `true` and `Z`), one (as with `S`), or more than one,
as here:

> data NatProd : Type where
>   Pair : Nat -> Nat -> NatProd

This declaration can be read: "There is just one way to construct a pair of
numbers: by applying the constructor `Pair` to two arguments of type `Nat`."

```idris
λΠ> :t Pair 3 5
```

Here are two simple functions for extracting the first and second components of
a pair. The definitions also illustrate how to do pattern matching on
two-argument constructors.

> fst : (p : NatProd) -> Nat
> fst (Pair x y) = x

> snd : (p : NatProd) -> Nat
> snd (Pair x y) = y

```idris
λΠ> fst (Pair 3 5)
-- 3 : Nat
```

Since pairs are used quite a bit, it is nice to be able to write them with the
standard mathematical notation `(x,y)` instead of `Pair x y`. We can tell Idris
to allow this with a `syntax` declaration.

> syntax "(" [x] "," [y] ")" = Pair x y

The new pair notation can be used both in expressions and in pattern matches
(indeed, we've actually seen this already in the previous chapter, in the
definition of the `minus` function -- this works because the pair notation is
also provided as part of the standard library):

```idris λΠ>
fst_pair (3,5)
-- 3 : Nat
```

> fst' : (p : NatProd) -> Nat
> fst' (x,y) = x

> snd' : (p : NatProd) -> Nat
> snd' (x,y) = y

> swap_pair : (p : NatProd) -> NatProd
> swap_pair (x,y) = (y,x)

Let's try to prove a few simple facts about pairs.

If we state things in a particular (and slightly peculiar) way, we can complete
proofs with just reflexivity (and its built-in simplification):

> surjective_pairing' : (n,m : Nat) -> (n,m) = (fst (n,m), snd (n,m))
> surjective_pairing' n m = Refl

But `Refl` is not enough if we state the lemma in a more natural way:

```idris
surjective_pairing_stuck : (p : NatProd) -> p = (fst p, snd p)
surjective_pairing_stuck p = Refl
```
```
When checking right hand side of
  surjective_pairing_stuck with expected type p = Pair (fst p) (snd p)
...
Type mismatch between p and Pair (fst p) (snd p)
```

We have to expose the structure of `p` so that `simpl` can perform the pattern
match in `fst` and `snd`. We can do this with `case`.

> surjective_pairing : (p : NatProd) -> p = (fst p, snd p)
> surjective_pairing p = case p of (n,m) => Refl

Notice that `case` matches just one pattern here. That's because `NatProd`s can
only be constructed in one way.


=== Exercise: 1 star (snd_fst_is_swap)

> snd_fst_is_swap : (p : NatProd) -> (snd p, fst p) = swap_pair p
> snd_fst_is_swap p = ?snd_fst_is_swap_rhs

$\square$


=== Exercise: 1 star, optional (fst_swap_is_snd)

> fst_swap_is_snd : (p : NatProd) -> fst (swap_pair p) = snd p
> fst_swap_is_snd p = ?fst_swap_is_snd_rhs

$\square$


== Lists of Numbers

Generalizing the definition of pairs, we can describe the type of _lists_ of
numbers like this: "A list is either the empty list or else a pair of a number
and another list."

> data NatList : Type where
>   Nil : NatList
>   Cons : Nat -> NatList -> NatList

For example, here is a three-element list:

> mylist : NatList
> mylist = Cons 1 (Cons 2 (Cons 3 Nil))

As with pairs, it is more convenient to write lists in familiar programming
notation. The following declarations allow us to use `::` as an infix Cons
operator and square brackets as an "outfix" notation for constructing lists.

> syntax [x] "::" [l] = Cons x l
> syntax "[ ]" = Nil

\todo[inline]{Figure out `syntax` command for this and edit the section}
Notation "[ x ; .. ; y ]" := ( cons x .. ( cons y nil ) ..).

It is not necessary to understand the details of these declarations, but in case
you are interested, here is roughly what's going on. The right associativity
annotation tells Coq how to parenthesize expressions involving several uses of
:: so that, for example, the next three declarations mean exactly the same
thing:

> mylist1 : NatList
> mylist1 = 1 :: (2 :: (3 :: Nil))

> mylist2 : NatList
> mylist2 = 1::2::3::Nil

Definition mylist3 := [1;2;3].

The at level 60 part tells Coq how to parenthesize expressions that involve both
:: and some other infix operator. For example, since we defined + as infix
notation for the plus function at level 50,

Notation "x + y" := ( plus x y )
( at level 50, left associativity ).

the + operator will bind tighter than :: , so 1 + 2 :: [3] will be parsed, as
we'd expect, as (1 + 2) :: [3] rather than 1 + (2 :: [3]) .

(Expressions like "1 + 2 :: [3]" can be a little confusing when you read them
in a .v file. The inner brackets, around 3, indicate a list, but the outer
brackets, which are invisible in the HTML rendering, are there to instruct the
"coqdoc" tool that the bracketed part should be displayed as Coq code rather
than running text.)

The second and third Notation declarations above introduce the standard
square-bracket notation for lists; the right-hand side of the third one
illustrates Coq's syntax for declaring n-ary notations and translating them to
nested sequences of binary constructors.


=== Repeat

A number of functions are useful for manipulating lists. For example, the
`repeat` function takes a number `n` and a `count` and returns a list of length
`count` where every element is `n`.

> repeat : (n, count : Nat) -> NatList
> repeat n Z = Nil
> repeat n (S k) = n :: repeat n k


=== Length

The `length` function calculates the length of a list.

> length : (l : NatList) -> Nat
> length Nil = Z
> length (h :: t) = S (length t)


=== Append

The `app` function concatenates (appends) two lists.

> app : (l1, l2 : NatList) -> NatList
> app Nil l2 = l2
> app (h :: t) l2 = h :: app t l2

Actually, `app` will be used a lot in some parts of what follows, so it is
convenient to have an infix operator for it.

> syntax [x] "++" [y] = app x y

> test_app1 : ((1::2::3::[]) ++ (4::5::[])) = (1::2::3::4::5::[])
> test_app1 = Refl

> test_app2 : ([] ++ (4::5::[])) = (4::5::[])
> test_app2 = Refl

> test_app3 : ((1::2::3::[]) ++ []) = (1::2::3::[])
> test_app3 = Refl


=== Head (with default) and Tail

Here are two smaller examples of programming with lists. The `hd` function
returns the first element (the "head") of the list, while `tl` returns
everything but the first element (the "tail"). Of course, the empty list has no
first element, so we must pass a default value to be returned in that case.

> hd : (default : Nat) -> (l : NatList) -> Nat
> hd default Nil = default
> hd default (h :: t) = h

> tl : (l : NatList) -> NatList
> tl Nil = Nil
> tl (h :: t) = t

> test_hd1 : hd 0 (1::2::3::[]) = 1
> test_hd1 = Refl

> test_hd2 : hd 0 [] = 0
> test_hd2 = Refl

> test_tl : tl (1::2::3::[]) = (2::3::[])
> test_tl = Refl


=== Exercises

==== Exercise: 2 stars, recommended (list_funs)

Complete the definitions of `nonzeros`, `oddmembers` and `countoddmembers`
below. Have a look at the tests to understand what these functions should do.

> nonzeros : (l : NatList) -> NatList
> nonzeros l = ?nonzeros_rhs

> test_nonzeros : nonzeros (0::1::0::2::3::0::0::[]) = (1::2::3::[])
> test_nonzeros = ?test_nonzeros_rhs

> oddmembers : (l : NatList) -> NatList
> oddmembers l = ?oddmembers_rhs

> test_oddmembers : oddmembers (0::1::0::2::3::0::0::[]) = (1::3::[])
> test_oddmembers = ?test_oddmembers_rhs

> countoddmembers : (l : NatList) -> Nat
> countoddmembers l = ?countoddmembers_rhs

> test_countoddmembers1 : countoddmembers (1::0::3::1::4::5::[]) = 4
> test_countoddmembers1 = ?test_countoddmembers1_rhs

$\square$


==== Exercise: 3 stars, advanced (alternate)

Complete the definition of `alternate`, which "zips up" two lists into one,
alternating between elements taken from the first list and elements from the
second. See the tests below for more specific examples.

Note: one natural and elegant way of writing `alternate` will fail to satisfy
Idris's requirement that all function definitions be "obviously terminating." If
you find yourself in this rut, look for a slightly more verbose solution that
considers elements of both lists at the same time. (One possible solution
requires defining a new kind of pairs, but this is not the only way.)

> alternate : (l1, l2 : NatList) -> NatList
> alternate l1 l2 = ?alternate_rhs

> test_alternate1 : alternate (1::2::3::[]) (4::5::6::[]) =
>                             (1::4::2::5::3::6::[])
> test_alternate1 = ?test_alternate1_rhs

> test_alternate2 : alternate (1::[]) (4::5::6::[]) = (1::4::5::6::[])
> test_alternate2 = ?test_alternate2_rhs

> test_alternate3 : alternate (1::2::3::[]) (4::[]) = (1::4::2::3::[])
> test_alternate3 = ?test_alternate3_rhs

> test_alternate4 : alternate [] (20::30::[]) = (20::30::[])
> test_alternate4 = ?test_alternate4_rhs

$\square$


=== Bags via Lists

A `bag` (or `multiset`) is like a set, except that each element can appear
multiple times rather than just once. One possible implementation is to
represent a bag of numbers as a list.

> Bag : Type
> Bag = NatList


==== Exercise: 3 stars, recommended (bag_functions)

Complete the following definitions for the functions `count`, `sum`, `add`, and
`member` for bags.

> count : (v : Nat) -> (s : Bag) -> Nat
> count v s = ?count_rhs

All these proofs can be done just by `Refl`.

> test_count1 : count 1 (1::2::3::1::4::1::[]) = 3
> test_count1 = ?test_count1_rhs

> test_count2 : count 6 (1::2::3::1::4::1::[]) = 0
> test_count2 = ?test_count2_rhs

Multiset `sum` is similar to set `union`: `sum a b` contains all the elements of
`a` and of `b`. (Mathematicians usually define union on multisets a little bit
differently, which is why we don't use that name for this operation.)

\todo[inline]{How to forbid recursion here? Edit}
For `sum` we're giving you a header that does not give explicit names to the
arguments. Moreover, it uses the keyword Definition instead of Fixpoint, so
even if you had names for the arguments, you wouldn't be able to process them
recursively. The point of stating the question this way is to encourage you to
think about whether sum can be implemented in another way -- perhaps by using
functions that have already been defined.

> sum : Bag -> Bag -> Bag
> sum x y = ?sum_rhs

> test_sum1 : count 1 (sum (1::2::3::[]) (1::4::1::[])) = 3
> test_sum1 = ?test_sum1_rhs

> add : (v : Nat) -> (s : Bag) -> Bag
> add v s = ?add_rhs

> test_add1 : count 1 (add 1 (1::4::1::[])) = 3
> test_add1 = ?test_add1_rhs

> test_add2 : count 5 (add 1 (1::4::1::[])) = 0
> test_add2 = ?test_add2_rhs

> member : (v : Nat) -> (s : Bag) -> Bool
> member v s = ?member_rhs

> test_member1 : member 1 (1::4::1::[]) = True
> test_member1 = ?test_member1_rhs

> test_member2 : member 2 (1::4::1::[]) = False
> test_member2 = ?test_member2_rhs

$\square$


==== Exercise: 3 stars, optional (bag_more_functions)

Here are some more bag functions for you to practice with.

When `remove_one` is applied to a bag without the number to remove, it should
return the same bag unchanged.

> remove_one : (v : Nat) -> (s : Bag) -> Bag
> remove_one v s = ?remove_one_rhs

> test_remove_one1 : count 5 (remove_one 5 (2::1::5::4::1::[])) = 0
> test_remove_one1 = ?test_remove_one1_rhs

> test_remove_one2 : count 5 (remove_one 5 (2::1::4::1::[])) = 0
> test_remove_one2 = ?test_remove_one2_rhs

> test_remove_one3 : count 4 (remove_one 5 (2::1::5::4::1::4::[])) = 2
> test_remove_one3 = ?test_remove_one3_rhs

> test_remove_one4 : count 5 (remove_one 5 (2::1::5::4::5::1::4::[])) = 1
> test_remove_one4 = ?test_remove_one4_rhs

> remove_all : (v : Nat) -> (s : Bag) -> Bag
> remove_all v s = ?remove_all_rhs

> test_remove_all1 : count 5 (remove_all 5 (2::1::5::4::1::[])) = 0
> test_remove_all1 = ?test_remove_all1_rhs

> test_remove_all2 : count 5 (remove_all 5 (2::1::4::1::[])) = 0
> test_remove_all2 = ?test_remove_all2_rhs

> test_remove_all3 : count 4 (remove_all 5 (2::1::5::4::1::4::[])) = 2
> test_remove_all3 = ?test_remove_all3_rhs

> test_remove_all4 : count 5
>                    (remove_all 5 (2::1::5::4::5::1::4::5::1::4::[])) = 0
> test_remove_all4 = ?test_remove_all4_rhs

> subset : (s1 : Bag) -> (s2 : Bag) -> Bool
> subset s1 s2 = ?subset_rhs

> test_subset1 : subset (1::2::[]) (2::1::4::1::[]) = True
> test_subset1 = ?test_subset1_rhs

> test_subset2 : subset (1::2::2::[]) (2::1::4::1::[]) = False
> test_subset2 = ?test_subset2_rhs

$\square$


==== Exercise: 3 stars, recommended (bag_theorem)

Write down an interesting theorem `bag_theorem` about bags involving the
functions `count` and `add`, and prove it. Note that, since this problem is
somewhat open-ended, it's possible that you may come up with a theorem which is
true, but whose proof requires techniques you haven't learned yet. Feel free to
ask for help if you get stuck!

> bag_theorem : ?bag_theorem

$\square$


== Reasoning About Lists

As with numbers, simple facts about list-processing functions can sometimes be
proved entirely by simplification. For example, the simplification performed by
`Refl` is enough for this theorem...

> nil_app : (l : NatList) -> ([] ++ l) = l
> nil_app l = Refl

... because the `[]` is substituted into the "scrutinee" (the value being
"scrutinized" by the match) in the definition of `app`, allowing the match
itself to be simplified.

Also, as with numbers, it is sometimes helpful to perform case analysis on the
possible shapes (empty or non-empty) of an unknown list.

> tl_length_pred : (l : NatList) -> pred (length l) = length (tl l)
> tl_length_pred Nil = Refl
> tl_length_pred (Cons n l') = Refl

Here, the `Nil` case works because we've chosen to define `tl Nil = Nil`. Notice
that the case for `Cons` introduces two names, `n` and `l'`, corresponding to
the fact that the `Cons` constructor for lists takes two arguments (the head and
tail of the list it is constructing).

Usually, though, interesting theorems about lists require induction for their
proofs.


==== Micro-Sermon

Simply reading example proof scripts will not get you very far! It is important
to work through the details of each one, using Idris and thinking about what
each step achieves. Otherwise it is more or less guaranteed that the exercises
will make no sense when you get to them. 'Nuff said.


=== Induction on Lists

Proofs by induction over datatypes like `NatList` are a little less familiar
than standard natural number induction, but the idea is equally simple. Each
`data` declaration defines a set of data values that can be built up using the
declared constructors: a boolean can be either `True` or `False` ; a number can
be either `Z` or `S` applied to another number; a list can be either `Nil` or
`Cons` applied to a number and a list.

Moreover, applications of the declared constructors to one another are the
_only_ possible shapes that elements of an inductively defined set can have, and
this fact directly gives rise to a way of reasoning about inductively defined
sets: a number is either `Z` or else it is `S` applied to some _smaller_ number;
a list is either `Nil` or else it is `Cons` applied to some number and some
_smaller_ list; etc. So, if we have in mind some proposition `P` that mentions a
list `l` and we want to argue that `P` holds for _all_ lists, we can reason as
follows:

  - First, show that `P` is true of `l` when `l` is `Nil`.

  - Then show that `P` is true of `l` when `l` is `cons n l'` for some number
    `n` and some smaller list `l'`, assuming that `P` is true for `l'`.

Since larger lists can only be built up from smaller ones, eventually reaching
`Nil`, these two arguments together establish the truth of `P` for all lists
`l`. Here's a concrete example:

> app_assoc : (l1, l2, l3 : NatList) -> ((l1 ++ l2) ++ l3) = (l1 ++ (l2 ++ l3))
> app_assoc Nil l2 l3 = Refl
> app_assoc (Cons n l1') l2 l3 =
>   let inductiveHypothesis = app_assoc l1' l2 l3 in
>     rewrite inductiveHypothesis in Refl

\todo[inline]{Edit}
Notice that, as when doing induction on natural numbers, the as ... clause
provided to the induction tactic gives a name to the induction hypothesis
corresponding to the smaller list l1' in the cons case. Once again, this Coq
proof is not especially illuminating as a static written document -- it is easy
to see what's going on if you are reading the proof in an interactive Coq
session and you can see the current goal and context at each point, but this
state is not visible in the written-down parts of the Coq proof. So a
natural-language proof -- one written for human readers -- will need to include
more explicit signposts; in particular, it will help the reader stay oriented if
we remind them exactly what the induction hypothesis is in the second case.

For comparison, here is an informal proof of the same theorem.

_Theorem_: For all lists `l1`, `l2`, and `l3`,
           `(l1 ++ l2) ++ l3 = l1 ++ (l2 ++l3)`.

_Proof_: By induction on `l1`.

  - First, suppose `l1 = []`. We must show
    `([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),`
    which follows directly from the definition of `++`.

  - Next, suppose `l1 = n :: l1'`, with
    `(l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)`
    (the induction hypothesis). We must show
    `((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3)`.
    By the definition of `++`, this follows from
    `n :: ((l1' ++ l2) ++ l 3) = n :: (l1' ++ (l2 ++ l3))`,
    which is immediate from the induction hypothesis. $\square$


==== Reversing a List

For a slightly more involved example of inductive proof over lists, suppose we
use `app` to define a list-reversing function `rev`:

> rev : (l : NatList) -> NatList
> rev Nil = Nil
> rev (h :: t) = (rev t) ++ (h::[])

> test_rev1 : rev (1::2::3::[]) = (3::2::1::[])
> test_rev1 = Refl

> test_rev2 : rev Nil = Nil
> test_rev2 = Refl


==== Properties of rev

Now let's prove some theorems about our newly defined `rev`. For something a bit
more challenging than what we've seen, let's prove that reversing a list does
not change its length. Our first attempt gets stuck in the successor case...

```idris
rev_length_firsttry : (l : NatList) -> length (rev l) = length l
rev_length_firsttry Nil = Refl
rev_length_firsttry (n :: l') =
-- Now we seem to be stuck: the goal is an equality involving `++`, but we don't
-- have any useful equations in either the immediate context or in the global
-- environment! We can make a little progress by using the IH to rewrite the
-- goal...
  let inductiveHypothesis = rev_length_firsttry l' in
    rewrite inductiveHypothesis in
-- ... but now we can't go any further.
      Refl
```

So let's take the equation relating `++` and `length` that would have enabled us
to make progress and prove it as a separate lemma.

> app_length : (l1, l2 : NatList) ->
>               length (l1 ++ l2) = (length l1) + (length l2)
> app_length Nil l2 = Refl
> app_length (n :: l1') l2 =
>   let inductiveHypothesis = app_length l1' l2 in
>     rewrite inductiveHypothesis in
>       Refl

Note that, to make the lemma as general as possible, we quantify over _all_
`NatList`s, not just those that result from an application of `rev`. This should
seem natural, because the truth of the goal clearly doesn't depend on the list
having been reversed. Moreover, it is easier to prove the more general property.

Now we can complete the original proof.

> rev_length : (l : NatList) -> length (rev l) = length l
> rev_length Nil = Refl
> rev_length (n :: l') =
>   rewrite app_length (rev l') (n::[]) in
> -- Prelude's version of `Induction.plus_comm`
>     rewrite plusCommutative (length (rev l')) 1 in
>       let inductiveHypothesis = rev_length l' in
>         rewrite inductiveHypothesis in Refl

For comparison, here are informal proofs of these two theorems:

_Theorem_: For all lists `l1` and `l2`,
           `length (l1 ++ l2) = length l1 + length l2`.

_Proof_: By induction on `l1`.

  - First, suppose `l1 = []`. We must show
    `length ([] ++ l2) = length [] + length l2`,
    which follows directly from the definitions of `length` and `++`.

  - Next, suppose `l1 = n :: l1'`, with
    `length (l1' ++ l2) = length l1' + length l2`.
    We must show
    `length ((n :: l1') ++ l2) = length (n :: l1') + length l2)`.
    This follows directly from the definitions of `length` and `++` together
    with the induction hypothesis. $\square$

_Theorem_: For all lists `l`, `length (rev l) = length l`.

_Proof_: By induction on `l`.

  - First, suppose `l = []`. We must show
    `length (rev []) = length []`,
    which follows directly from the definitions of `length` and `rev`.

  - Next, suppose l = n :: l' , with
    `length (rev l') = length l'`.
    We must show
    `length (rev (n :: l')) = length (n :: l')`.
    By the definition of `rev`, this follows from
    `length ((rev l') ++ [n]) = S (length l')`
    which, by the previous lemma, is the same as
    `length (rev l') + length [n] = S (length l')`.
    This follows directly from the induction hypothesis and the definition of
    `length`. $\square$

The style of these proofs is rather longwinded and pedantic. After the first
few, we might find it easier to follow proofs that give fewer details (which can
easily work out in our own minds or on scratch paper if necessary) and just
highlight the non-obvious steps. In this more compressed style, the above proof
might look like this:

_Theorem_: For all lists `l`, `length (rev l) = length l`.

_Proof_: First, observe that length `(l ++ [n]) = S (length l)` for any `l`
(this follows by a straightforward induction on `l`). The main property again
follows by induction on `l`, using the observation together with the induction
hypothesis in the case where `l = n' :: l'`. $\square$

Which style is preferable in a given situation depends on the sophistication of
the expected audience and how similar the proof at hand is to ones that the
audience will already be familiar with. The more pedantic style is a good
default for our present purposes.

\todo[inline]{Edit: `apropos`?}
=== Search

We've seen that proofs can make use of other theorems we've already proved,
e.g., using rewrite . But in order to refer to a theorem, we need to know its
name! Indeed, it is often hard even to remember what theorems have been proven,
much less what they are called.

Coq's Search command is quite helpful with this. Typing Search foo will cause
Coq to display a list of all theorems involving foo . For example, try
uncommenting the following line to see a list of theorems that we have proved
about rev :

(* Search rev. *)

Keep Search in mind as you do the following exercises and throughout the rest of
the book; it can save you a lot of time!

If you are using ProofGeneral, you can run Search with C-c C-a C-a. Pasting its
response into your buffer can be accomplished with C-c C-;.


=== List Exercises, Part 1

==== Exercise: 3 stars (list_exercises)

More practice with lists:

> app_nil_r : (l : NatList) -> (l ++ []) = l
> app_nil_r l = ?app_nil_r_rhs

> rev_app_distr : (l1, l2 : NatList) -> rev (l1 ++ l2) = (rev l2) ++ (rev l1)
> rev_app_distr l1 l2 = ?rev_app_distr_rhs

> rev_involutive : (l : NatList) -> rev (rev l) = l
> rev_involutive l = ?rev_involutive_rhs

There is a short solution to the next one. If you find yourself getting tangled
up, step back and try to look for a simpler way.

> app_assoc4 : (l1, l2, l3, l4 : NatList) ->
>              (l1 ++ (l2 ++ (l3 ++ l4))) = ((l1 ++ l2) ++ l3) ++ l4
> app_assoc4 l1 l2 l3 l4 = ?app_assoc4_rhs

An exercise about your implementation of `nonzeros`:

> nonzeros_app : (l1, l2 : NatList) ->
>                 nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2)
> nonzeros_app l1 l2 = ?nonzeros_app_rhs

$\square$


==== Exercise: 2 stars (beq_NatList)

Fill in the definition of `beq_NatList`, which compares lists of numbers for
equality. Prove that `beq_NatList l l` yields `True` for every list `l`.

> beq_NatList : (l1, l2 : NatList) -> Bool
> beq_NatList l1 l2 = ?beq_NatList_rhs

> test_beq_NatList1 : beq_NatList Nil Nil = True
> test_beq_NatList1 = ?test_beq_NatList1_rhs

> test_beq_NatList2 : beq_NatList (1::2::3::[]) (1::2::3::[]) = True
> test_beq_NatList2 = ?test_beq_NatList2_rhs

> test_beq_NatList3 : beq_NatList (1::2::3::[]) (1::2::4::[]) = False
> test_beq_NatList3 = ?test_beq_NatList3_rhs

> beq_NatList_refl : (l : NatList) -> True = beq_NatList l l
> beq_NatList_refl l = ?beq_NatList_refl_rhs

$\square$


=== List Exercises, Part 2

==== Exercise: 3 stars, advanced (bag_proofs)

Here are a couple of little theorems to prove about your definitions about bags
above.

> count_member_nonzero : (s : Bag) -> leb 1 (count 1 (1 :: s)) = True
> count_member_nonzero s = ?count_member_nonzero_rhs

The following lemma about `leb` might help you in the next proof.

> ble_n_Sn : (n : Nat) -> leb n (S n) = True
> ble_n_Sn Z = Refl
> ble_n_Sn (S k) =
>   let inductiveHypothesis = ble_n_Sn k in
>     rewrite inductiveHypothesis in Refl

> remove_decreases_count : (s : Bag) ->
>                          leb (count 0 (remove_one 0 s)) (count 0 s) = True
> remove_decreases_count s = ?remove_decreases_count_rhs

$\square$


==== Exercise: 3 stars, optional (bag_count_sum)

Write down an interesting theorem `bag_count_sum` about bags involving the
functions `count` and `sum`, and prove it. (You may find that the difficulty of
the proof depends on how you defined `count`!)

> bag_count_sum : ?bag_count_sum

$\square$


==== Exercise: 4 stars, advanced (rev_injective)

Prove that the `rev` function is injective -- that is,

> rev_injective : (l1, l2 : NatList) -> rev l1 = rev l2 -> l1 = l2
> rev_injective l1 l2 prf = ?rev_injective_rhs

(There is a hard way and an easy way to do this.)

$\square$


== Options

Suppose we want to write a function that returns the `n`th element of some list.
If we give it type `Nat -> NatList -> Nat`, then we'll have to choose some
number to return when the list is too short...

> nth_bad : (l : NatList) -> (n : Nat) -> Nat
> nth_bad Nil n = 42 -- arbitrary!
> nth_bad (a :: l') n = case beq_nat n 0 of
>                         True => a
>                         False => nth_bad l' (pred n)

This solution is not so good: If `nth_bad` returns `42`, we can't tell whether
that value actually appears on the input without further processing. A better
alternative is to change the return type of `nth_bad` to include an error value
as a possible outcome. We call this type `NatOption`.

> data NatOption : Type where
>   Some : Nat -> NatOption
>   None : NatOption

We can then change the above definition of `nth_bad` to return `None` when the
list is too short and `Some a` when the list has enough members and `a` appears
at position `n`. We call this new function `nth_error` to indicate that it may
result in an error.

> nth_error : (l : NatList) -> (n : Nat) -> NatOption
> nth_error Nil n = None
> nth_error (a :: l') n = case beq_nat n 0 of
>                           True => Some a
>                           False => nth_error l' (pred n)

> test_nth_error1 : nth_error (4::5::6::7::[]) 0 = Some 4
> test_nth_error1 = Refl

> test_nth_error2 : nth_error (4::5::6::7::[]) 3 = Some 7
> test_nth_error2 = Refl

> test_nth_error3 : nth_error (4::5::6::7::[]) 9 = None
> test_nth_error3 = Refl

This example is also an opportunity to introduce one more small feature of Idris
programming language: conditional expressions...

> nth_error' : (l : NatList) -> (n : Nat) -> NatOption
> nth_error' Nil n = None
> nth_error' (a :: l') n = if beq_nat n 0
>                            then Some a
>                            else nth_error' l' (pred n)

\todo[inline]{Edit this paragraph}
Coq's conditionals are exactly like those found in any other language, with one
small generalization. Since the boolean type is not built in, Coq actually
supports conditional expressions over any inductively defined type with exactly
two constructors. The guard is considered true if it evaluates to the first
constructor in the Inductive definition and false if it evaluates to the second.

The function below pulls the `Nat` out of a `NatOption`, returning a supplied
default in the `None` case.

> option_elim : (d : Nat) -> (o : NatOption) -> Nat
> option_elim d (Some k) = k
> option_elim d None = d


==== Exercise: 2 stars (hd_error)

Using the same idea, fix the `hd` function from earlier so we don't have to pass
a default element for the `Nil` case.

> hd_error : (l : NatList) -> NatOption
> hd_error l = ?hd_error_rhs

> test_hd_error1 : hd_error [] = None
> test_hd_error1 = ?test_hd_error1_rhs

> test_hd_error2 : hd_error (1::[]) = Some 1
> test_hd_error2 = ?test_hd_error2_rhs

> test_hd_error3 : hd_error (5::6::[]) = Some 5
> test_hd_error3 = ?test_hd_error3_rhs

$\square$


==== Exercise: 1 star, optional (option_elim_hd)

This exercise relates your new `hd_error` to the old `hd`.

> option_elim_hd : (l : NatList) -> (default : Nat) ->
>                  hd default l = option_elim default (hd_error l)
> option_elim_hd l default = ?option_elim_hd_rhs

$\square$


== Partial Maps

As a final illustration of how data structures can be defined in Idris, here is
a simple _partial map_ data type, analogous to the map or dictionary data
structures found in most programming languages.

First, we define a new inductive datatype `Id` to serve as the "keys" of our
partial maps.

> data Id : Type where
>   MkId : Nat -> Id

Internally, an `Id` is just a number. Introducing a separate type by wrapping
each `Nat` with the tag `MkId` makes definitions more readable and gives us the
flexibility to change representations later if we wish.

We'll also need an equality test for `Id`s:

> beq_id : (x1, x2 : Id) -> Bool
> beq_id (MkId n1) (MkId n2) = beq_nat n1 n2


==== Exercise: 1 star (beq_id_refl)

> beq_id_refl : (x : Id) -> True = beq_id x x

$\square$

Now we define the type of partial maps:

> namespace PartialMap

>   data PartialMap : Type where
>     Empty : PartialMap
>     Record : Id -> Nat -> PartialMap -> PartialMap

This declaration can be read: "There are two ways to construct a `PartialMap`:
either using the constructor `Empty` to represent an empty partial map, or by
applying the constructor `Record` to a key, a value, and an existing
`PartialMap` to construct a `PartialMap` with an additional key-to-value
mapping."

The `update` function overrides the entry for a given key in a partial map (or
adds a new entry if the given key is not already present).

>   update : (d : PartialMap) -> (x : Id) -> (value : Nat) -> PartialMap
>   update d x value = Record x value d

Last, the `find` function searches a `PartialMap` for a given key. It returns
`None` if the key was not found and `Some val` if the key was associated with
`val`. If the same key is mapped to multiple values, `find` will return the
first one it encounters.

>   find : (x : Id) -> (d : PartialMap) -> NatOption
>   find x Empty = None
>   find x (Record y v d') = if beq_id x y
>                              then Some v
>                              else find x d'


==== Exercise: 1 star (update_eq)

>   update_eq : (d : PartialMap) -> (x : Id) -> (v : Nat) ->
>               find x (update d x v) = Some v
>   update_eq d x v = ?update_eq_rhs

$\square$


==== Exercise: 1 star (update_neq)

>   update_neq : (d : PartialMap) -> (x, y : Id ) -> (o : Nat) ->
>                 beq_id x y = False ->
>                 find x (update d y o) = find x d
>   update_neq d x y o prf = ?update_neq_rhs

$\square$


==== Exercise: 2 stars (baz_num_elts)

Consider the following inductive definition:

> data Baz : Type where
>   Baz1 : Baz -> Baz
>   Baz2 : Baz -> Bool -> Baz

How _many_ elements does the type `Baz` have? (Answer in English or the natural
language of your choice.)

$\square$
