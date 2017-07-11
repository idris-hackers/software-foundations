= Poly: Polymorphism and Higher-Order Functions

> import Basics

> %hide Prelude.List.length
> %hide Prelude.List.filter
> %hide Prelude.List.partition
> %hide Prelude.Functor.map
> %hide Prelude.Nat.pred
> %hide Basics.Playground2.plus

> %access public export

> %default total


== Polymorphism

In this chapter we continue our development of basic concepts of functional
programming. The critical new ideas are _polymorphism_ (abstracting functions
over the types of the data they manipulate) and _higher-order functions_
(treating functions as data). We begin with polymorphism.


=== Polymorphic Lists

For the last couple of chapters, we've been working just with lists of numbers.
Obviously, interesting programs also need to be able to manipulate lists with
elements from other types -- lists of strings, lists of booleans, lists of
lists, etc. We _could_ just define a new inductive datatype for each of these,
for example...

> data BoolList : Type where
>   BoolNil : BoolList 
>   BoolCons : Bool -> BoolList -> BoolList

... but this would quickly become tedious, partly because we have to make up
different constructor names for each datatype, but mostly because we would also
need to define new versions of all our list manipulating functions (`length`,
`rev`, etc.) for each new datatype definition. 

To avoid all this repetition, Idris supports _polymorphic_ inductive type
definitions. For example, here is a _polymorphic list_ datatype.

```idris
data List : (x : Type) -> Type where
  Nil : List x 
  Cons : x -> List x -> List x
```

(This type is already defined in Idris' standard library, but the `Cons` 
constructor is named `(::)`).

This is exactly like the definition of `NatList` from the previous chapter,
except that the `Nat` argument to the `Cons` constructor has been replaced by an
arbitrary type `x`, a binding for `x` has been added to the header, and the
occurrences of `NatList` in the types of the constructors have been replaced by
`List x`. (We can re-use the constructor names `Nil` and `Cons` because the
earlier definition of `NatList` was inside of a `module` definition that is now
out of scope.) 

What sort of thing is `List` itself? One good way to think about it is that
`List` is a _function_ from `Type`s to inductive definitions; or, to put it
another way, `List` is a function from `Type`s to `Type`s. For any particular
type `x`, the type `List x` is an inductively defined set of lists whose
elements are of type `x`. 

With this definition, when we use the constructors `Nil` and `Cons` to build
lists, we need to tell Idris the type of the elements in the lists we are
building -- that is, `Nil` and `Cons` are now _polymorphic constructors_.
Observe the types of these constructors:

```idris 
λΠ> :t Nil
-- Prelude.List.Nil : List elem
λΠ> :t (::)
-- Prelude.List.(::) : elem -> List elem -> List elem
```

\todo[inline]{How to edit these 3 paragraphs? Implicits are defined later in
this chapter, and Idris doesn't require type parameters to constructors} 
(Side note on notation: In .v files, the "forall" quantifier is spelled out in
letters. In the generated HTML files and in the way various IDEs show .v files
(with certain settings of their display controls), ∀ is usually typeset as the
usual mathematical "upside down A," but you'll still see the spelled-out
"forall" in a few places. This is just a quirk of typesetting: there is no
difference in meaning.) 

The "∀ X" in these types can be read as an additional argument to the
constructors that determines the expected types of the arguments that follow.
When `Nil` and `Cons` are used, these arguments are supplied in the same way as
the others. For example, the list containing `2` and `1` is written like this:

Check (cons nat 2 (cons nat 1 (nil nat))).

(We've written `Nil` and `Cons` explicitly here because we haven't yet defined
the `[]` and `::` notations for the new version of lists. We'll do that in a
bit.) 

We can now go back and make polymorphic versions of all the list-processing
functions that we wrote before. Here is `repeat`, for example:

> repeat : (x_ty : Type) -> (x : x_ty) -> (count : Nat) -> List x_ty
> repeat x_ty x Z = Nil
> repeat x_ty x (S count') = x :: repeat x_ty x count'

As with `Nil` and `Cons`, we can use `repeat` by applying it first to a type and
then to its list argument:

> test_repeat1 : repeat Nat 4 2 = 4 :: (4 :: Nil)
> test_repeat1 = Refl

To use `repeat` to build other kinds of lists, we simply instantiate it with an
appropriate type parameter:

> test_repeat2 : repeat Bool False 1 = False :: Nil
> test_repeat2 = Refl


\todo[inline]{Explain implicits and {x=foo} syntax first? Move after the
"Supplying Type Arguments Explicitly" section?} 

==== Exercise: 2 starsM (mumble_grumble) 

> namespace MumbleGrumble 

Consider the following two inductively defined types.

>   data Mumble : Type where
>     A : Mumble 
>     B : Mumble -> Nat -> Mumble
>     C : Mumble

>   data Grumble : (x : Type) -> Type where
>     D : Mumble -> Grumble x 
>     E : x -> Grumble x

Which of the following are well-typed elements of `Grumble x` for some type `x`?

  - `D (B A 5)`
  - `D (B A 5) {x=Mumble}`
  - `D (B A 5) {x=Bool}`
  - `E True {x=Bool}`
  - `E (B C 0) {x=Mumble}`
  - `E (B C 0) {x=Bool}`
  - `C`
  
> -- FILL IN HERE

$\square$

\todo[inline]{Merge 3 following sections into one about Idris implicits? Mention
the lowercase/uppercase distinction.}

==== Type Annotation Inference 

\todo[inline]{This has already happened earlier at `repeat`, delete most of
this?}

Let's write the definition of `repeat` again, but this time we won't specify the
types of any of the arguments. Will Idris still accept it?

Fixpoint repeat' X x count : list X :=
  match count with | 0 ⇒ nil X | S count' ⇒ cons X x (repeat' X x count') end.

Indeed it will. Let's see what type Idris has assigned to `repeat'`:

Check repeat'. (* ===> forall X : Type, X -> nat -> list X *) Check repeat. (*
===> forall X : Type, X -> nat -> list X *)

It has exactly the same type type as `repeat`. Idris was able to use _type
inference_ to deduce what the types of `X`, `x`, and `count` must be, based on
how they are used. For example, since `X` is used as an argument to `Cons`, it
must be a `Type`, since `Cons` expects a `Type` as its first argument; matching
`count` with `Z` and `S` means it must be a `Nat`; and so on.

This powerful facility means we don't always have to write explicit type
annotations everywhere, although explicit type annotations are still quite
useful as documentation and sanity checks, so we will continue to use them most
of the time. You should try to find a balance in your own code between too many
type annotations (which can clutter and distract) and too few (which forces
readers to perform type inference in their heads in order to understand your
code).


==== Type Argument Synthesis

\todo[inline]{We should mention the `_` parameters but it won't work like this
in Idris}

To use a polymorphic function, we need to pass it one or more types in addition
to its other arguments. For example, the recursive call in the body of the
`repeat` function above must pass along the type `x_ty`. But since the second
argument to `repeat` is an element of `x_ty`, it seems entirely obvious that the
first argument can only be `x_ty` — why should we have to write it explicitly?

Fortunately, Idris permits us to avoid this kind of redundancy. In place of any
type argument we can write the "implicit argument" `_`, which can be read as
"Please try to figure out for yourself what belongs here." More precisely, when
Idris encounters a `_`, it will attempt to _unify_ all locally available
information -- the type of the function being applied, the types of the other
arguments, and the type expected by the context in which the application appears
-- to determine what concrete type should replace the `_`. 

This may sound similar to type annotation inference -- indeed, the two
procedures rely on the same underlying mechanisms. Instead of simply omitting
the types of some arguments to a function, like

      repeat' X x count : list X :=

we can also replace the types with `_`

      repeat' (X : _) (x : _) (count : _) : list X :=

to tell Idris to attempt to infer the missing information. 

Using implicit arguments, the `count` function can be written like this:

Fixpoint repeat'' X x count : list X :=
  match count with | 0 ⇒ nil _ | S count' ⇒ cons _ x (repeat'' _ x count') end.

In this instance, we don't save much by writing `_` instead of `x`. But in many
cases the difference in both keystrokes and readability is nontrivial. For
example, suppose we want to write down a list containing the numbers `1`, `2`,
and `3`. Instead of writing this...

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

...we can use argument synthesis to write this:

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).


==== Implicit Arguments

We can go further and even avoid writing `_`'s in most cases by telling Idris
_always_ to infer the type argument(s) of a given function. The Arguments
directive specifies the name of the function (or constructor) and then lists its
argument names, with curly braces around any arguments to be treated as
implicit. (If some arguments of a definition don't have a name, as is often the
case for constructors, they can be marked with a wildcard pattern _.)

Arguments nil {X}. Arguments cons {X} _ _. Arguments repeat {X} x count.

Now, we don't have to supply type arguments at all:

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Alternatively, we can declare an argument to be implicit when defining the
function itself, by surrounding it in curly braces instead of parens. For
example:

> repeat' : {x_ty : Type} -> (x : x_ty) -> (count : Nat) -> List x_ty 
> repeat' x Z = Nil
> repeat' x (S count') = x :: repeat' x count'

(Note that we didn't even have to provide a type argument to the recursive call
to `repeat'`; indeed, it would be invalid to provide one!) 

We will use the latter style whenever possible, but we will continue to use
explicit declarations in data types. The reason for this is that marking the
parameter of an inductive type as implicit causes it to become implicit for the
type itself, not just for its constructors. For instance, consider the following
alternative definition of the `List` type:

> data List' : {x : Type} -> Type where
>   Nil' : List' 
>   Cons' : x -> List' -> List'

Because `x` is declared as implicit for the _entire_ inductive definition
including `List'` itself, we now have to write just `List'` whether we are
talking about lists of numbers or booleans or anything else, rather than `List'
Nat` or `List' Bool` or whatever; this is a step too far. 

\todo[inline]{Added the implicit inference explanation here}
There's another step towards conciseness that we can take in Idris -- drop the
implicit argument completely in function definitions! Idris will automatically
insert them for us when it encounters unknown variables. _Note that by convention
this will only happen for variables starting on a lowercase letter_.
 
> repeat'' : (x : x_ty) -> (count : Nat) -> List x_ty 
> repeat'' x Z = Nil
> repeat'' x (S count') = x :: repeat'' x count'

Let's finish by re-implementing a few other standard list functions on our new
polymorphic lists...

> app : (l1, l2 : List x) -> List x 
> app Nil l2 = l2
> app (h::t) l2 = h :: app t l2

> rev : (l: List x) -> List x
> rev [] = []
> rev (h::t) = app (rev t) (h::Nil)

> length : (l : List x) -> Nat 
> length [] = Z
> length (_::l') = S (length l')

> test_rev1 : rev (1::2::[]) = 2::1::[]
> test_rev1 = Refl

> test_rev2: rev (True::[]) = True::[]
> test_rev2 = Refl

> test_length1: length (1::2::3::[]) = 3
> test_length1 = Refl


==== Supplying Type Arguments Explicitly 

One small problem with declaring arguments implicit is that, occasionally, Idris
does not have enough local information to determine a type argument; in such
cases, we need to tell Idris that we want to give the argument explicitly just
this time. For example, suppose we write this:

```idris
λΠ> :let mynil = Nil
-- (input):Can't infer argument elem to []
```

Here, Idris gives us an error because it doesn't know what type argument to
supply to `Nil`. We can help it by providing an explicit type declaration via
`the` function (so that Idris has more information available when it gets to the
"application" of `Nil`):

```idris
λΠ> :let mynil = the (List Nat) Nil
```

Alternatively, we can force the implicit arguments to be explicit by supplying
them as arguments in curly braces. 

```idris
λΠ> :let mynil' = Nil {elem=Nat}
```

\todo[inline]{Describe here how to bring variables from the type into definition
scope via implicits?}

\todo[inline]{Explain that Idris has built-in notation for lists instead?}

Using argument synthesis and implicit arguments, we can define convenient
notation for lists, as before. Since we have made the constructor type arguments
implicit, Coq will know to automatically infer these when we use the notations.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil. Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Now lists can be written just the way we'd hope:

> list123''' : List Nat
> list123''' = [1, 2, 3]


==== Exercise: 2 stars, optional (poly_exercises)

Here are a few simple exercises, just like ones in the `Lists` chapter, for
practice with polymorphism. Complete the proofs below.

> app_nil_r : (l : List x) -> l ++ [] = l
> app_nil_r l = ?app_nil_r_rhs

> app_assoc : (l, m, n : List a) -> l ++ m ++ n = (l ++ m) ++ n
> app_assoc l m n = ?app_assoc_rhs

> app_length : (l1, l2 : List x) -> length (l1 ++ l2) = length l1 + length l2
> app_length l1 l2 = ?app_length_rhs

$\square$


==== Exercise: 2 stars, optional (more_poly_exercises) 

Here are some slightly more interesting ones...

> rev_app_distr: (l1, l2 : List x) -> rev (l1 ++ l2) = rev l2 ++ rev l1
> rev_app_distr l1 l2 = ?rev_app_distr_rhs

> rev_involutive : (l : List x) -> rev (rev l) = l
> rev_involutive l = ?rev_involutive_rhs

$\square$


=== Polymorphic Pairs

Following the same pattern, the type definition we gave in the last chapter for
pairs of numbers can be generalized to _polymorphic pairs_, often called
_products_:

> data Prod : (x, y : Type) -> Type where
>   PPair : x -> y -> Prod x y

As with lists, we make the type arguments implicit and define the familiar
concrete notation.

> syntax "(" [x] "," [y] ")" = PPair x y

We can also use the `syntax` mechanism to define the standard notation for
product _types_:

> syntax [x_ty] "*" [y_ty] = Prod x_ty y_ty

(The annotation : type_scope tells Coq that this abbreviation should only be
used when parsing types. This avoids a clash with the multiplication symbol.) 

It is easy at first to get `(x,y)` and `x_ty*y_ty` confused. Remember that
`(x,y)` is a value built from two other values, while `x_ty*y_ty` is a type
built from two other types. If `x` has type `x` and `y` has type `y`, then
`(x,y)` has type `x_ty*y_ty`. 

The first and second projection functions now look pretty much as they would in
any functional programming language.

> fst : (p : x*y) -> x
> fst (x,y) = x

> snd : (p : x*y) -> y
> snd (x,y) = y
  
The following function takes two lists and combines them into a list of pairs.
In functional languages, it is usually called `zip` (though the Coq's standard
library calls it `combine`).

> zip : (lx : List x) -> (ly : List y) -> List (x*y)
> zip [] _ = []
> zip _ [] = []
> zip (x::tx) (y::ty) = (x,y) :: zip tx ty


==== Exercise: 1 star, optionalM (combine_checks)

Try answering the following questions on paper and checking your answers in
Idris: 

- What is the type of `zip` (i.e., what does `:t zip` print?) 

- What does

  `combine [1,2] [False,False,True,True]`

  print? 

$\square$


==== Exercise: 2 stars, recommended (split) 

The function `split` is the right inverse of `zip`: it takes a list of pairs and
returns a pair of lists. In many functional languages, it is called `unzip`. 

Fill in the definition of `split` below. Make sure it passes the given unit
test.

> split : (l : List (x*y)) -> (List x) * (List y)
> split l = ?split_rhs

> test_split: split [(1,False),(2,False)] = ([1,2],[False,False])
> test_split = ?test_split_rhs

$\square$


==== Polymorphic Options

One last polymorphic type for now: _polymorphic options_, which generalize
`NatOption` from the previous chapter:

> data Option : (x : Type) -> Type where
>  Some : x -> Option x
>  None : Option x

In Idris' standard library this type is called `Maybe`, with constructors `Just
x` and `Nothing`.

We can now rewrite the `nth_error` function so that it works with any type of
lists.

> nth_error : (l : List x) -> (n : Nat) -> Option x 
> nth_error [] n = None
> nth_error (a::l') n = if beq_nat n 0 
>                         then Some a
>                         else nth_error l' (pred n)

> test_nth_error1 : nth_error [4,5,6,7] 0 = Some 4
> test_nth_error1 = Refl

> test_nth_error2 : nth_error [[1],[2]] 1 = Some [2]
> test_nth_error2 = Refl

> test_nth_error3 : nth_error [True] 2 = None
> test_nth_error3 = Refl


==== Exercise: 1 star, optional (hd_error_poly)

Complete the definition of a polymorphic version of the `hd_error` function from
the last chapter. Be sure that it passes the unit tests below.

> hd_error : (l : List x) -> Option x
> hd_error l = ?hd_error_rhs

> test_hd_error1 : hd_error [1,2] = Some 1
> test_hd_error1 = ?test_hd_error1_rhs

> test_hd_error2 : hd_error [[1],[2]] = Some [1]
> test_hd_error2 = ?test_hd_error2_rhs

$\square$


== Functions as Data

Like many other modern programming languages -- including all functional
languages (ML, Haskell, Scheme, Scala, Clojure etc.) -- Idris treats functions
as first-class citizens, allowing them to be passed as arguments to other
functions, returned as results, stored in data structures, etc.


=== Higher-Order Functions

Functions that manipulate other functions are often called _higher-order_
functions. Here's a simple one:

> doit3times : (f: x -> x) -> (n : x) -> x
> doit3times f n = f (f (f n))

The argument `f` here is itself a function (from `x` to `x`); the body of
`doit3times` applies `f` three times to some value `n`.

```idris
λΠ> :t doit3times
-- doit3times : (x -> x) -> x -> x
```

> test_doit3times : doit3times Numbers.minusTwo 9 = 3
> test_doit3times = Refl

> test_doit3times': doit3times Booleans.negb True = False
> test_doit3times' = Refl


=== Filter

Here is a more useful higher-order function, taking a list of `x`s and a
_predicate_ on `x` (a function from `x` to `Bool`) and "filtering" the list,
returning a new list containing just those elements for which the predicate
returns `True`.

> filter : (test : x -> Bool) -> (l: List x) -> List x
> filter test [] = []
> filter test (h::t) = if test h
>                       then h :: (filter test t)
>                       else filter test t

For example, if we apply `filter` to the predicate `evenb` and a list of numbers
`l`, it returns a list containing just the even members of `l`.

> test_filter1 : filter Numbers.evenb [1,2,3,4] = [2,4]
> test_filter1 = Refl

> length_is_1 : (l : List x) -> Bool 
> length_is_1 l = beq_nat (length l) 1

\todo[inline]{Why doesn't this work without {x=Nat}?}

> test_filter2 : filter (length_is_1 {x=Nat})
>                       [ [1,2], [3], [4], [5,6,7], [], [8] ]
>                     = [        [3], [4],              [8] ]
> test_filter2 = Refl 

We can use `filter` to give a concise version of the `countoddmembers` function
from the `Lists` chapter.

> countoddmembers' : (l: List Nat) -> Nat
> countoddmembers' l = length (filter Numbers.oddb l)

> test_countoddmembers'1 : countoddmembers' [1,0,3,1,4,5] = 4
> test_countoddmembers'1 = Refl

> test_countoddmembers'2 : countoddmembers' [0,2,4] = 0
> test_countoddmembers'2 = Refl

> test_countoddmembers'3 : countoddmembers' Nil = 0
> test_countoddmembers'3 = Refl


=== Anonymous Functions

It is arguably a little sad, in the example just above, to be forced to define
the function `length_is_1` and give it a name just to be able to pass it as an
argument to `filter`, since we will probably never use it again. Moreover, this
is not an isolated example: when using higher-order functions, we often want to
pass as arguments "one-off" functions that we will never use again; having to
give each of these functions a name would be tedious.

Fortunately, there is a better way. We can construct a function "on the fly"
without declaring it at the top level or giving it a name.

\todo[inline]{Can't use `*` here due to the interference from our tuple sugar}

> test_anon_fun': doit3times (\n => mult n n) 2 = 256
> test_anon_fun' = Refl

The expression `\n => mult n n` can be read as "the function that, given a
number `n`, yields `n * n`."

Here is the `filter` example, rewritten to use an anonymous function.

> test_filter2': filter (\l => beq_nat (length l) 1)
>                       [ [1,2], [3], [4], [5,6,7], [], [8] ]
>                     = [        [3], [4],              [8] ]
> test_filter2' = Refl


==== Exercise: 2 stars (filter_even_gt7)

Use `filter` (instead of function definition) to write an Idris function
`filter_even_gt7` that takes a list of natural numbers as input and returns a
list of just those that are even and greater than `7`.

> filter_even_gt7 : (l : List Nat) -> List Nat
> filter_even_gt7 l = ?filter_even_gt7_rhs

> test_filter_even_gt7_1 : filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8]
> test_filter_even_gt7_1 = ?test_filter_even_gt7_1_rhs

> test_filter_even_gt7_2 : filter_even_gt7 [5,2,6,19,129] = []
> test_filter_even_gt7_2 = ?test_filter_even_gt7_2_rhs

$\square$


==== Exercise: 3 stars (partition)

Use `filter` to write an Idris function `partition`:

> partition : (test: x -> Bool) -> (l : List x) -> (List x) * (List x)
> partition f xs = ?partition_rhs

Given a set `x`, a test function of type `x -> Bool` and a `List x`, `partition`
should return a pair of lists. The first member of the pair is the sublist of
the original list containing the elements that satisfy the test, and the second
is the sublist containing those that fail the test. The order of elements in the
two sublists should be the same as their order in the original list.

> test_partition1 : partition Numbers.oddb [1,2,3,4,5] = ([1,3,5], [2,4])
> test_partition1 = ?test_partition1_rhs

> test_partition2: partition (\x => false) [5,9,0] = (([], [5,9,0]))
> test_partition2 = ?test_partition2_rhs

$\square$


=== Map 

Another handy higher-order function is called `map`.

> map : (f : x -> y) -> (l : List x) -> List y
> map f [] = []
> map f (h::t) = (f h) :: map f t

It takes a function `f` and a list `l = [n1, n2, n3, ...]` and returns the list
`[f n1, f n2, f n3,...]`, where `f` has been applied to each element of `l` in
turn. For example:

> test_map1 : map (\x => plus 3 x) [2,0,2] = [5,3,5]
> test_map1 = Refl

The element types of the input and output lists need not be the same, since
`map` takes _two_ type arguments, `x` and `y`; it can thus be applied to a list
of numbers and a function from numbers to booleans to yield a list of booleans:

> test_map2 : map Numbers.oddb [2,1,2,5] = [False,True,False,True]
> test_map2 = Refl

It can even be applied to a list of numbers and a function from numbers to
_lists_ of booleans to yield a _list of lists_ of booleans:

> test_map3 : map (\n => [evenb n, oddb n]) [2,1,2,5]
>                   = [[True,False],[False,True],[True,False],[False,True]]
> test_map3 = Refl


==== Exercise: 3 stars (map_rev)

Show that `map` and `rev` commute. You may need to define an auxiliary lemma.

> map_rev : (f : x -> y) -> (l : List x) -> map f (rev l) = rev (map f l)
> map_rev f l = ?map_rev_rhs

$\square$


==== Exercise: 2 stars, recommended (flat_map)

The function `map` maps a `List x` to a `List y` using a function of type `x ->
y`. We can define a similar function, `flat_map`, which maps a `List x` to a
`List y` using a function `f` of type `X -> List y`. Your definition should work
by 'flattening' the results of `f`, like so:

```idris
flat_map (\n => [n,n+1,n+2]) [1,5,10] = [1,2,3, 5,6,7, 10,11,12]
```

> flat_map : (f: x -> List y) -> (l : List x) -> List y
> flat_map f l = ?flat_map_rhs

> test_flat_map1: flat_map (\n => [n,n,n]) [1,5,4] = [1,1,1, 5,5,5, 4,4,4]
> test_flat_map1 = ?test_flat_map1_rhs

$\square$

Lists are not the only inductive type that we can write a `map` function for.
Here is the definition of `map` for the `Option` type:

> option_map : (f : x -> y) -> (xo : Option x) -> Option y
> option_map f None = None
> option_map f (Some x) = Some (f x)


==== Exercise: 2 stars, optional (implicit_args)

The definitions and uses of `filter` and `map` use implicit arguments in many
places. Add explicit type parameters where necessary and use Idris to check that
you've done so correctly. (This exercise is not to be turned in; it is probably
easiest to do it on a copy of this file that you can throw away afterwards.) 

$\square$


=== Fold

An even more powerful higher-order function is called `fold`. This function is
the inspiration for the `"reduce"` operation that lies at the heart of Google's
map/reduce distributed programming framework.

> fold : (f : x -> y -> y) -> (l : List x) -> (b : y) -> y
> fold f [] b = b
> fold f (h::t) b = f h (fold f t b)

Intuitively, the behavior of the `fold` operation is to insert a given binary
operator `f` between every pair of elements in a given list. For example, `fold
plus [1;2;3;4]` intuitively means `1+2+3+4`. To make this precise, we also need
a "starting element" that serves as the initial second input to `f`. So, for
example,

`fold plus [1,2,3,4] 0`

yields

`1 + (2 + (3 + (4 + 0)))`

Some more examples:

```idris
λΠ> :t fold andb
-- fold andb : List Bool -> Bool -> Bool
```

> fold_example1 : fold Nat.mult [1,2,3,4] 1 = 24
> fold_example1 = Refl

> fold_example2 : fold Booleans.andb [True,True,False,True] True = False
> fold_example2 = Refl

> fold_example3 : fold (++) [[1],[],[2,3],[4]] [] = [1,2,3,4]
> fold_example3 = Refl


==== Exercise: 1 star, advancedM (fold_types_different)

Observe that the type of `fold` is parameterized by _two_ type variables, `x`
and `y`, and the parameter `f` is a binary operator that takes an `x` and a `y`
and returns a `y`. Can you think of a situation where it would be useful for `x`
and `y` to be different?

-- FILL IN HERE

$\square$


=== Functions That Construct Functions

Most of the higher-order functions we have talked about so far take functions as
arguments. Let's look at some examples that involve _returning_ functions as the
results of other functions. To begin, here is a function that takes a value `x`
(drawn from some type `x`) and returns a function from `Nat` to `x` that yields
`x` whenever it is called, ignoring its `Nat` argument.

> constfun : (x : x_ty) -> Nat -> x_ty 
> constfun x = \k => x

> ftrue : Nat -> Bool
> ftrue = constfun True

> constfun_example1 : ftrue 0 = True
> constfun_example1 = Refl

> constfun_example2 : (constfun 5) 99 = 5
> constfun_example2 = Refl

In fact, the multiple-argument functions we have already seen are also examples
of passing functions as data. To see why, recall the type of `plus`.

```idris
λΠ> :t plus
Prelude.Nat.plus : Nat -> Nat -> Nat
```

Each `->` in this expression is actually a _binary_ operator on types. This
operator is _right-associative_, so the type of `plus` is really a shorthand for
`Nat -> (Nat -> Nat)` -- i.e., it can be read as saying that "`plus` is a
one-argument function that takes a `Nat` and returns a one-argument function
that takes another `Nat` and returns a `Nat`." In the examples above, we have
always applied `plus` to both of its arguments at once, but if we like we can
supply just the first. This is called _partial application_.

> plus3 : Nat -> Nat
> plus3 = plus 3

```idris
λΠ> :t plus3
```

> test_plus3 : plus3 4 = 7
> test_plus3 = Refl

\todo[inline]{Why is this broken? `the (doit3times plus3 0 = 9) Refl` works in
REPL}

> -- test_plus3' : doit3times plus3 0 = 9
> -- test_plus3' = Refl

> test_plus3'' : doit3times (plus 3) 0 = 9
> test_plus3'' = Refl


== Additional Exercises

> namespace Exercises


==== Exercise: 2 stars (fold_length)

Many common functions on lists can be implemented in terms of `fold`. For
example, here is an alternative definition of `length`:

>   fold_length : (l : List x) -> Nat 
>   fold_length l = fold (\_, n => S n) l 0

>   test_fold_length1 : fold_length [4,7,0] = 3
>   test_fold_length1 = Refl

Prove the correctness of `fold_length`.

>   fold_length_correct : (l : List x) -> fold_length l = length l
>   fold_length_correct l = ?fold_length_correct_rhs

$\square$


==== Exercise: 3 starsM (fold_map)

We can also define `map` in terms of fold. Finish `fold_map` below.

>   fold_map : (f : x -> y) -> (l : List x) -> List y
>   fold_map f l = ?fold_map_rhs

Write down a theorem `fold_map_correct` in Idris stating that `fold_map` is
correct, and prove it.

>   fold_map_correct : ?fold_map_correct

$\square$


==== Exercise: 2 stars, advanced (currying)

In Idris, a function `f: a -> b -> c` really has the type `a -> (b -> c)`. That
is, if you give `f` a value of type `a`, it will give you function `f' : b ->
c`. If you then give `f'` a value of type `b`, it will return a value of type
`c`. This allows for partial application, as in `plus3`. Processing a list of
arguments with functions that return functions is called _currying_, in honor of
the logician Haskell Curry. 

Conversely, we can reinterpret the type `a -> b -> c` as `(a * b) -> c`. This is
called _uncurrying_. With an uncurried binary function, both arguments must be
given at once as a pair; there is no partial application.

We can define currying as follows:

>   prod_curry : (f : (x * y) -> z) -> (x_val : x) -> (y_val : y) -> z
>   prod_curry f x_val y_val = f (x_val, y_val)

As an exercise, define its inverse, `prod_uncurry`. Then prove the theorems
below to show that the two are inverses.

>   prod_uncurry : (f : x -> y -> z) -> (p : x * y) -> z 
>   prod_uncurry f p = ?prod_uncurry_rhs

As a (trivial) example of the usefulness of currying, we can use it to shorten
one of the examples that we saw above:

\todo[inline]{Not sure what are they shortening here}

>   test_map2' : map (\x => plus 3 x) [2,0,2] = [5,3,5]
>   test_map2' = Refl

\todo[inline]{Didn't we just write out these types explicitly?}

Thought exercise: before running the following commands, can you calculate the
types of `prod_curry` and `prod_uncurry`?

```idris
λΠ> :t prod_curry
λΠ> :t prod_uncurry
```

>   uncurry_curry : (f : x -> y -> z) -> (x_val : x) -> (y_val : y) -> 
>                   prod_curry (prod_uncurry f) x_val y_val = f x_val y_val
>   uncurry_curry f x_val y_val = ?uncurry_curry_rhs

>   curry_uncurry : (f : (x * y) -> z) -> (p : x * y) -> 
>                   prod_uncurry (prod_curry f) p = f p
>   curry_uncurry f p = ?curry_uncurry_rhs

$\square$


==== Exercise: 2 stars, advancedM (nth_error_informal)

Recall the definition of the `nth_error` function:

```idris
  nth_error : (l : List x) -> (n : Nat) -> Option x 
  nth_error [] n = None
  nth_error (a::l') n = if beq_nat n 0 
                          then Some a
                          else nth_error l' (pred n)
```

Write an informal proof of the following theorem:

  `n -> l -> length l = n -> nth_error l n = None`
  
  -- FILL IN HERE

$\square$


==== Exercise: 4 stars, advanced (church_numerals)

This exercise explores an alternative way of defining natural numbers, using the
so-called _Church numerals_, named after mathematician Alonzo Church. We can
represent a natural number `n` as a function that takes a function `f` as a
parameter and returns `f` iterated `n` times.

> namespace Church

>   Nat' : {x : Type} -> Type
>   Nat' {x} = (x -> x) -> x -> x

Let's see how to write some numbers with this notation. Iterating a function
once should be the same as just applying it. Thus:

>   one : Nat'
>   one f x = f x

Similarly, `two` should apply `f` twice to its argument:

>   two : Nat'
>   two f x = f (f x)

Defining `zero` is somewhat trickier: how can we "apply a function zero times"?
The answer is actually simple: just return the argument untouched.

>   zero : Nat'
>   zero f x = x

More generally, a number `n` can be written as `\f, x => f (f ... (f x) ...)`,
with `n` occurrences of `f`. Notice in particular how the `doit3times` function
we've defined previously is actually just the Church representation of `3`.

>   three : Nat'
>   three = doit3times

Complete the definitions of the following functions. Make sure that the
corresponding unit tests pass by proving them with `Refl`. 

Successor of a natural number:

>   succ : (n : Nat') -> Nat'
>   succ n = ?succ_rhs

>   succ_1 : succ zero = one
>   succ_1 = ?succ_1_rhs

>   succ_2 : succ one = two
>   succ_2 = ?succ_2_rhs

>   succ_3 : succ two = three
>   succ_3 = ?succ_3_rhs

Addition of two natural numbers:

>   plus' : (n, m : Nat') -> Nat'
>   plus' n m = ?plus'_rhs

>   plus'_1 : plus' zero one = one
>   plus'_1 = ?plus'_1_rhs

>   plus'_2 : plus' two three = plus' three two
>   plus'_2 = ?plus'_2_rhs

>   plus'_3 : plus' (plus' two two) three = plus' one (plus' three three)
>   plus'_3 = ?plus'_3_rhs

Multiplication:

>   mult' : (n, m : Nat') -> Nat'
>   mult' n m = ?mult'_rhs

>   mult'_1 : mult' one one = one
>   mult'_1 = ?mult'_1_rhs

>   mult'_2 : mult' zero (plus' three three) = zero
>   mult'_2 = ?mult'_2_rhs

>   mult'_3 : mult' two three = plus' three three
>   mult'_3 = ?mult'_3_rhs

Exponentiation: 

\todo[inline]{Edit the hint.}

(Hint: Polymorphism plays a crucial role here. However, choosing the right type
to iterate over can be tricky. If you hit a "Universe inconsistency" error, try
iterating over a different type: `Nat'` itself is usually problematic.)

>   exp' : (n, m : Nat') -> Nat'
>   exp' n m = ?exp'_rhs

>   exp'_1 : exp' two two = plus' two two
>   exp'_1 = ?exp'_1_rhs

>   exp'_2 : exp' three two = plus' (mult' two (mult' two two)) one
>   exp'_2 = ?exp'_2_rhs

>   exp'_3 : exp' three zero = one
>   exp'_3 = ?exp'_3_rhs

$\square$
