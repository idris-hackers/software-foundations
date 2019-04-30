= Poly : Polymorphism and Higher-Order Functions

> module Poly

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
need to define new versions of all our list manipulating functions
(\idr{length}, \idr{rev}, etc.) for each new datatype definition.

To avoid all this repetition, Idris supports _polymorphic_ inductive type
definitions. For example, here is a _polymorphic list_ datatype.

```idris
data List : (x : Type) -> Type where
  Nil : List x
  Cons : x -> List x -> List x
```

(This type is already defined in Idris' standard library, but the \idr{Cons}
constructor is named \idr{(::)}).

This is exactly like the definition of \idr{NatList} from the previous chapter,
except that the \idr{Nat} argument to the \idr{Cons} constructor has been
replaced by an arbitrary type \idr{x}, a binding for \idr{x} has been added to
the header, and the occurrences of \idr{NatList} in the types of the
constructors have been replaced by \idr{List x}. (We can re-use the constructor
names \idr{Nil} and \idr{Cons} because the earlier definition of \idr{NatList}
was inside of a \idr{namespace} definition that is now out of scope.)

What sort of thing is \idr{List} itself? One good way to think about it is that
\idr{List} is a _function_ from \idr{Type}s to inductive definitions; or, to put
it another way, \idr{List} is a function from \idr{Type}s to \idr{Type}s. For
any particular type \idr{x}, the type \idr{List x} is an inductively defined set
of lists whose elements are of type \idr{x}.

With this definition, when we use the constructors \idr{Nil} and \idr{Cons} to
build lists, we need to tell Idris the type of the elements in the lists we are
building -- that is, \idr{Nil} and \idr{Cons} are now _polymorphic
constructors_. Observe the types of these constructors:

```idris
λΠ> :t Nil
Prelude.List.Nil : List elem
λΠ> :t (::)
Prelude.List.(::) : elem -> List elem -> List elem
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
When \idr{Nil} and \idr{Cons} are used, these arguments are supplied in the same
way as the others. For example, the list containing \idr{2} and \idr{1} is
written like this:

Check (cons nat 2 (cons nat 1 (nil nat))).

(We've written \idr{Nil} and \idr{Cons} explicitly here because we haven't yet
defined the \idr{[]} and \idr{::} notations for the new version of lists. We'll
do that in a bit.)

We can now go back and make polymorphic versions of all the list-processing
functions that we wrote before. Here is \idr{repeat}, for example:

> repeat : (x_ty : Type) -> (x : x_ty) -> (count : Nat) -> List x_ty
> repeat x_ty x Z = Nil
> repeat x_ty x (S count') = x :: repeat x_ty x count'

As with \idr{Nil} and \idr{Cons}, we can use \idr{repeat} by applying it first
to a type and then to its list argument:

> test_repeat1 : repeat Nat 4 2 = 4 :: (4 :: Nil)
> test_repeat1 = Refl

To use \idr{repeat} to build other kinds of lists, we simply instantiate it with
an appropriate type parameter:

> test_repeat2 : repeat Bool False 1 = False :: Nil
> test_repeat2 = Refl


==== Exercise: 2 stars (mumble_grumble)

\ \todo[inline]{Explain implicits and \idr{{x=foo}} syntax first? Move after the
"Supplying Type Arguments Explicitly" section?}

> namespace MumbleGrumble

Consider the following two inductively defined types.

>   data Mumble : Type where
>     A : Mumble
>     B : Mumble -> Nat -> Mumble
>     C : Mumble

>   data Grumble : (x : Type) -> Type where
>     D : Mumble -> Grumble x
>     E : x -> Grumble x

Which of the following are well-typed elements of \idr{Grumble x} for some type
\idr{x}?

  - \idr{D (B A 5)}
  - \idr{D (B A 5) {x=Mumble}}
  - \idr{D (B A 5) {x=Bool}}
  - \idr{E True {x=Bool}}
  - \idr{E (B C 0) {x=Mumble}}
  - \idr{E (B C 0) {x=Bool}}
  - \idr{C}

> -- FILL IN HERE

$\square$

\todo[inline]{Merge 3 following sections into one about Idris implicits? Mention
the lowercase/uppercase distinction.}


==== Type Annotation Inference

\todo[inline]{This has already happened earlier at \idr{repeat}, delete most of
this?}

Let's write the definition of \idr{repeat} again, but this time we won't specify
the types of any of the arguments. Will Idris still accept it?

Fixpoint repeat' X x count : list X :=
  match count with | 0 ⇒ nil X | S count' ⇒ cons X x (repeat' X x count') end.

Indeed it will. Let's see what type Idris has assigned to \idr{repeat'}:

Check repeat'. (* ===> forall X : Type, X -> nat -> list X *) Check repeat. (*
===> forall X : Type, X -> nat -> list X *)

It has exactly the same type type as \idr{repeat}. Idris was able to use _type
inference_ to deduce what the types of \idr{X}, \idr{x}, and \idr{count} must
be, based on how they are used. For example, since \idr{X} is used as an
argument to \idr{Cons}, it must be a \idr{Type}, since \idr{Cons} expects a
\idr{Type} as its first argument; matching \idr{count} with \idr{Z} and \idr{S}
means it must be a \idr{Nat}; and so on.

This powerful facility means we don't always have to write explicit type
annotations everywhere, although explicit type annotations are still quite
useful as documentation and sanity checks, so we will continue to use them most
of the time. You should try to find a balance in your own code between too many
type annotations (which can clutter and distract) and too few (which forces
readers to perform type inference in their heads in order to understand your
code).


==== Type Argument Synthesis

\todo[inline]{We should mention the \idr{_} parameters but it won't work like
this in Idris}

To use a polymorphic function, we need to pass it one or more types in addition
to its other arguments. For example, the recursive call in the body of the
\idr{repeat} function above must pass along the type \idr{x_ty}. But since the
second argument to \idr{repeat} is an element of \idr{x_ty}, it seems entirely
obvious that the first argument can only be \idr{x_ty} — why should we have to
write it explicitly?

Fortunately, Idris permits us to avoid this kind of redundancy. In place of any
type argument we can write the "implicit argument" \idr{_}, which can be read as
"Please try to figure out for yourself what belongs here." More precisely, when
Idris encounters a \idr{_}, it will attempt to _unify_ all locally available
information -- the type of the function being applied, the types of the other
arguments, and the type expected by the context in which the application appears
-- to determine what concrete type should replace the \idr{_}.

This may sound similar to type annotation inference -- indeed, the two
procedures rely on the same underlying mechanisms. Instead of simply omitting
the types of some arguments to a function, like

      repeat' X x count : list X :=

we can also replace the types with \idr{_}

      repeat' (X : _) (x : _) (count : _) : list X :=

to tell Idris to attempt to infer the missing information.

Using implicit arguments, the \idr{count} function can be written like this:

Fixpoint repeat'' X x count : list X :=
  match count with | 0 ⇒ nil _ | S count' ⇒ cons _ x (repeat'' _ x count') end.

In this instance, we don't save much by writing \idr{_} instead of \idr{x}. But
in many cases the difference in both keystrokes and readability is nontrivial.
For example, suppose we want to write down a list containing the numbers
\idr{1}, \idr{2}, and \idr{3}. Instead of writing this...

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

...we can use argument synthesis to write this:

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).


==== Implicit Arguments

We can go further and even avoid writing \idr{_}'s in most cases by telling
Idris _always_ to infer the type argument(s) of a given function. The Arguments
directive specifies the name of the function (or constructor) and then lists its
argument names, with curly braces around any arguments to be treated as
implicit. (If some arguments of a definition don't have a name, as is often the
case for constructors, they can be marked with a wildcard pattern \idr{_}.)

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
to \idr{repeat'}; indeed, it would be invalid to provide one!)

We will use the latter style whenever possible, but we will continue to use
explicit declarations in data types. The reason for this is that marking the
parameter of an inductive type as implicit causes it to become implicit for the
type itself, not just for its constructors. For instance, consider the following
alternative definition of the \idr{List} type:

> data List' : {x : Type} -> Type where
>   Nil' : List'
>   Cons' : x -> List' -> List'

Because \idr{x} is declared as implicit for the _entire_ inductive definition
including \idr{List'} itself, we now have to write just \idr{List'} whether we
are talking about lists of numbers or booleans or anything else, rather than
\idr{List' Nat} or \idr{List' Bool} or whatever; this is a step too far.

\todo[inline]{Added the implicit inference explanation here}

There's another step towards conciseness that we can take in Idris -- drop the
implicit argument completely in function definitions! Idris will automatically
insert them for us when it encounters unknown variables. _Note that by
convention this will only happen for variables starting on a lowercase letter_.

> repeat'' : (x : x_ty) -> (count : Nat) -> List x_ty
> repeat'' x Z = Nil
> repeat'' x (S count') = x :: repeat'' x count'

Let's finish by re-implementing a few other standard list functions on our new
polymorphic lists...

> app : (l1, l2 : List x) -> List x
> app Nil l2 = l2
> app (h::t) l2 = h :: app t l2

> rev : (l : List x) -> List x
> rev [] = []
> rev (h::t) = app (rev t) (h::Nil)

> length : (l : List x) -> Nat
> length [] = Z
> length (_::l') = S (length l')

> test_rev1 : rev (1::2::[]) = 2::1::[]
> test_rev1 = Refl

> test_rev2 : rev (True::[]) = True::[]
> test_rev2 = Refl

> test_length1 : length (1::2::3::[]) = 3
> test_length1 = Refl


==== Supplying Type Arguments Explicitly

One small problem with declaring arguments implicit is that, occasionally, Idris
does not have enough local information to determine a type argument; in such
cases, we need to tell Idris that we want to give the argument explicitly just
this time. For example, suppose we write this:

```idris
λΠ> :let mynil = Nil
(input):Can't infer argument elem to []
```

Here, Idris gives us an error because it doesn't know what type argument to
supply to \idr{Nil}. We can help it by providing an explicit type declaration
via \idr{the} function (so that Idris has more information available when it
gets to the "application" of \idr{Nil}):

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

Here are a few simple exercises, just like ones in the \idr{Lists} chapter, for
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

> rev_app_distr : (l1, l2 : List x) -> rev (l1 ++ l2) = rev l2 ++ rev l1
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

\todo[inline]This sugar cannot be marked as private and messes up things when
imported, consider changing the notation}

> syntax "(" [x] "," [y] ")" = PPair x y

We can also use the \idr{syntax} mechanism to define the standard notation for
product _types_:

> syntax [x_ty] "*" [y_ty] = Prod x_ty y_ty

(The annotation : type_scope tells Coq that this abbreviation should only be
used when parsing types. This avoids a clash with the multiplication symbol.)

It is easy at first to get \idr{(x,y)} and \idr{x_ty*y_ty} confused. Remember
that \idr{(x,y)} is a value built from two other values, while \idr{x_ty*y_ty}
is a type built from two other types. If \idr{x} has type \idr{x_ty} and \idr{y}
has type \idr{y_ty}, then \idr{(x,y)} has type \idr{x_ty*y_ty}.

The first and second projection functions now look pretty much as they would in
any functional programming language.

> fst : (p : x*y) -> x
> fst (x,y) = x

> snd : (p : x*y) -> y
> snd (x,y) = y

\todo[inline]{Edit}

The following function takes two lists and combines them into a list of pairs.
In functional languages, it is usually called \idr{zip} (though the Coq's
standard library calls it \idr{combine}).

> zip : (lx : List x) -> (ly : List y) -> List (x*y)
> zip [] _ = []
> zip _ [] = []
> zip (x::tx) (y::ty) = (x,y) :: zip tx ty


==== Exercise: 1 star, optional (combine_checks)

Try answering the following questions on paper and checking your answers in
Idris:

- What is the type of \idr{zip} (i.e., what does \idr{:t zip} print?)

- What does \idr{combine [1,2] [False,False,True,True]} print?

$\square$


==== Exercise: 2 stars, recommended (split)

The function \idr{split} is the right inverse of \idr{zip}: it takes a list of
pairs and returns a pair of lists. In many functional languages, it is called
\idr{unzip}.

Fill in the definition of \idr{split} below. Make sure it passes the given unit
test.

> split : (l : List (x*y)) -> (List x) * (List y)
> split l = ?split_rhs

> test_split : split [(1,False),(2,False)] = ([1,2],[False,False])
> test_split = ?test_split_rhs

$\square$


==== Polymorphic Options

One last polymorphic type for now: _polymorphic options_, which generalize
\idr{NatOption} from the previous chapter:

> data Option : (x : Type) -> Type where
>  Some : x -> Option x
>  None : Option x

In Idris' standard library this type is called \idr{Maybe}, with constructors
\idr{Just x} and \idr{Nothing}.

We can now rewrite the \idr{nth_error} function so that it works with any type
of lists.

> nth_error : (l : List x) -> (n : Nat) -> Option x
> nth_error [] n = None
> nth_error (a::l') n = if n == 0
>                         then Some a
>                         else nth_error l' (pred n)

> test_nth_error1 : nth_error [4,5,6,7] 0 = Some 4
> test_nth_error1 = Refl

> test_nth_error2 : nth_error [[1],[2]] 1 = Some [2]
> test_nth_error2 = Refl

> test_nth_error3 : nth_error [True] 2 = None
> test_nth_error3 = Refl


==== Exercise: 1 star, optional (hd_error_poly)

Complete the definition of a polymorphic version of the \idr{hd_error} function
from the last chapter. Be sure that it passes the unit tests below.

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

The argument \idr{f} here is itself a function (from \idr{x} to \idr{x}); the
body of \idr{doit3times} applies \idr{f} three times to some value \idr{n}.

```idris
λΠ> :t doit3times
-- doit3times : (x -> x) -> x -> x
```

\todo[inline]{Explain that the prefixes are needed to avoid the implicit scoping
rule, seems that this fires up more often when passing functions as parameters
to other functions}

> test_doit3times : doit3times Numbers.minusTwo 9 = 3
> test_doit3times = Refl

> test_doit3times' : doit3times Bool.not True = False
> test_doit3times' = Refl


=== Filter

Here is a more useful higher-order function, taking a list of \idr{x}s and a
_predicate_ on \idr{x} (a function from \idr{x} to \idr{Bool}) and "filtering"
the list, returning a new list containing just those elements for which the
predicate returns \idr{True}.

> filter : (test : x -> Bool) -> (l: List x) -> List x
> filter test [] = []
> filter test (h::t) = if test h
>                       then h :: (filter test t)
>                       else filter test t

(This is how it's defined in Idris's stdlib, too.)

For example, if we apply \idr{filter} to the predicate \idr{evenb} and a list of
numbers \idr{l}, it returns a list containing just the even members of \idr{l}.

> test_filter1 : filter Numbers.evenb [1,2,3,4] = [2,4]
> test_filter1 = Refl

> length_is_1 : (l : List x) -> Bool
> length_is_1 l = length l == 1

> test_filter2 : filter Poly.length_is_1
>                       [ [1,2], [3], [4], [5,6,7], [], [8] ]
>                     = [        [3], [4],              [8] ]
> test_filter2 = Refl

We can use \idr{filter} to give a concise version of the \idr{countoddmembers}
function from the `Lists` chapter.

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
the function \idr{length_is_1} and give it a name just to be able to pass it as
an argument to \idr{filter}, since we will probably never use it again.
Moreover, this is not an isolated example: when using higher-order functions, we
often want to pass as arguments "one-off" functions that we will never use
again; having to give each of these functions a name would be tedious.

Fortunately, there is a better way. We can construct a function "on the fly"
without declaring it at the top level or giving it a name.

\todo[inline]{Can't use \idr{*} here due to the interference from our tuple
sugar}

> test_anon_fun' : doit3times (\n => mult n n) 2 = 256
> test_anon_fun' = Refl

The expression \idr{\n => mult n n} can be read as "the function that, given a
number \idr{n}, yields \idr{n * n}."

Here is the \idr{filter} example, rewritten to use an anonymous function.

> test_filter2' : filter (\l => length l == 1)
>                       [ [1,2], [3], [4], [5,6,7], [], [8] ]
>                     = [        [3], [4],              [8] ]
> test_filter2' = Refl


==== Exercise: 2 stars (filter_even_gt7)

Use \idr{filter} (instead of function definition) to write an Idris function
\idr{filter_even_gt7} that takes a list of natural numbers as input and returns
a list of just those that are even and greater than \idr{7}.

> filter_even_gt7 : (l : List Nat) -> List Nat
> filter_even_gt7 l = ?filter_even_gt7_rhs

> test_filter_even_gt7_1 : filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8]
> test_filter_even_gt7_1 = ?test_filter_even_gt7_1_rhs

> test_filter_even_gt7_2 : filter_even_gt7 [5,2,6,19,129] = []
> test_filter_even_gt7_2 = ?test_filter_even_gt7_2_rhs

$\square$


==== Exercise: 3 stars (partition)

Use \idr{filter} to write an Idris function \idr{partition}:

> partition : (test : x -> Bool) -> (l : List x) -> (List x) * (List x)
> partition f xs = ?partition_rhs

Given a set \idr{x}, a test function of type \idr{x -> Bool} and a \idr{List x},
\idr{partition} should return a pair of lists. The first member of the pair is
the sublist of the original list containing the elements that satisfy the test,
and the second is the sublist containing those that fail the test. The order of
elements in the two sublists should be the same as their order in the original
list.

> test_partition1 : partition Numbers.oddb [1,2,3,4,5] = ([1,3,5], [2,4])
> test_partition1 = ?test_partition1_rhs

> test_partition2 : partition (\x => False) [5,9,0] = (([], [5,9,0]))
> test_partition2 = ?test_partition2_rhs

$\square$


=== Map

Another handy higher-order function is called \idr{map}.

> map : (f : x -> y) -> (l : List x) -> List y
> map f [] = []
> map f (h::t) = (f h) :: map f t

It takes a function \idr{f} and a list \idr{l} = \idr{[n1, n2, n3, ...]} and
returns the list \idr{[f n1, f n2, f n3,...]}, where \idr{f} has been applied to
each element of \idr{l} in turn. For example:

> test_map1 : map (\x => plus 3 x) [2,0,2] = [5,3,5]
> test_map1 = Refl

The element types of the input and output lists need not be the same, since
\idr{map} takes _two_ type arguments, \idr{x} and \idr{y}; it can thus be
applied to a list of numbers and a function from numbers to booleans to yield a
list of booleans:

> test_map2 : map Numbers.oddb [2,1,2,5] = [False,True,False,True]
> test_map2 = Refl

It can even be applied to a list of numbers and a function from numbers to
_lists_ of booleans to yield a _list of lists_ of booleans:

> test_map3 : map (\n => [evenb n, oddb n]) [2,1,2,5]
>                   = [[True,False],[False,True],[True,False],[False,True]]
> test_map3 = Refl


==== Exercise: 3 stars (map_rev)

Show that \idr{map} and \idr{rev} commute. You may need to define an auxiliary
lemma.

> map_rev : (f : x -> y) -> (l : List x) -> map f (rev l) = rev (map f l)
> map_rev f l = ?map_rev_rhs

$\square$


==== Exercise: 2 stars, recommended (flat_map)

The function \idr{map} maps a \idr{List x} to a \idr{List y} using a function of
type \idr{x -> y}. We can define a similar function, \idr{flat_map}, which maps
a \idr{List x} to a \idr{List y} using a function \idr{f} of type \idr{x -> List
y}. Your definition should work by 'flattening' the results of \idr{f}, like so:

```idris
flat_map (\n => [n,n+1,n+2]) [1,5,10] = [1,2,3, 5,6,7, 10,11,12]
```

> flat_map : (f : x -> List y) -> (l : List x) -> List y
> flat_map f l = ?flat_map_rhs

> test_flat_map1 : flat_map (\n => [n,n,n]) [1,5,4] = [1,1,1, 5,5,5, 4,4,4]
> test_flat_map1 = ?test_flat_map1_rhs

$\square$

Lists are not the only inductive type that we can write a \idr{map} function
for. Here is the definition of \idr{map} for the \idr{Option} type:

> option_map : (f : x -> y) -> (xo : Option x) -> Option y
> option_map f None = None
> option_map f (Some x) = Some (f x)


==== Exercise: 2 stars, optional (implicit_args)

The definitions and uses of \idr{filter} and \idr{map} use implicit arguments in
many places. Add explicit type parameters where necessary and use Idris to check
that you've done so correctly. (This exercise is not to be turned in; it is
probably easiest to do it on a copy of this file that you can throw away
afterwards.)

$\square$


=== Fold

An even more powerful higher-order function is called \idr{fold}. This function
is the inspiration for the `"reduce"` operation that lies at the heart of
Google's map/reduce distributed programming framework.

> fold : (f : x -> y -> y) -> (l : List x) -> (b : y) -> y
> fold f [] b = b
> fold f (h::t) b = f h (fold f t b)

Intuitively, the behavior of the \idr{fold} operation is to insert a given
binary operator \idr{f} between every pair of elements in a given list. For
example, \idr{fold (+) [1,2,3,4]} intuitively means \idr{1+2+3+4}. To make this
precise, we also need a "starting element" that serves as the initial second
input to \idr{f}. So, for example,

\idr{fold (+) [1,2,3,4] 0}

yields

\idr{1 + (2 + (3 + (4 + 0)))}

Some more examples:

\todo[inline]{We go back to \idr{andb} here because \idr{(&&)}'s second
parameter is lazy, with the left fold the return type is inferred to be lazy
too, leading to type mismatch.}

```idris
λΠ> :t fold andb
fold andb : List Bool -> Bool -> Bool
```

> fold_example1 : fold (*) [1,2,3,4] 1 = 24
> fold_example1 = Refl

> fold_example2 : fold Booleans.andb [True,True,False,True] True = False
> fold_example2 = Refl

> fold_example3 : fold (++) [[1],[],[2,3],[4]] [] = [1,2,3,4]
> fold_example3 = Refl


==== Exercise: 1 star, advanced (fold_types_different)

Observe that the type of \idr{fold} is parameterized by _two_ type variables,
\idr{x} and \idr{y}, and the parameter \idr{f} is a binary operator that takes
an \idr{x} and a \idr{y} and returns a \idr{y}. Can you think of a situation
where it would be useful for \idr{x} and \idr{y} to be different?

> -- FILL IN HERE

$\square$


=== Functions That Construct Functions

Most of the higher-order functions we have talked about so far take functions as
arguments. Let's look at some examples that involve _returning_ functions as the
results of other functions. To begin, here is a function that takes a value
\idr{x} (drawn from some type \idr{x}) and returns a function from \idr{Nat} to
\idr{x} that yields \idr{x} whenever it is called, ignoring its \idr{Nat}
argument.

> constfun : (x : x_ty) -> Nat -> x_ty
> constfun x = \k => x

> ftrue : Nat -> Bool
> ftrue = constfun True

> constfun_example1 : ftrue 0 = True
> constfun_example1 = Refl

> constfun_example2 : (constfun 5) 99 = 5
> constfun_example2 = Refl

In fact, the multiple-argument functions we have already seen are also examples
of passing functions as data. To see why, recall the type of \idr{plus}.

```idris
λΠ> :t plus
Prelude.Nat.plus : Nat -> Nat -> Nat
```

Each \idr{->} in this expression is actually a _binary_ operator on types. This
operator is _right-associative_, so the type of \idr{plus} is really a shorthand
for \idr{Nat -> (Nat -> Nat)} -- i.e., it can be read as saying that "\idr{plus}
is a one-argument function that takes a \idr{Nat} and returns a one-argument
function that takes another \idr{Nat} and returns a \idr{Nat}." In the examples
above, we have always applied \idr{plus} to both of its arguments at once, but
if we like we can supply just the first. This is called _partial application_.

> plus3 : Nat -> Nat
> plus3 = plus 3

```idris
λΠ> :t plus3
```

> test_plus3 : plus3 4 = 7
> test_plus3 = Refl


> test_plus3' : doit3times Poly.plus3 0 = 9
> test_plus3' = Refl

> test_plus3'' : doit3times (plus 3) 0 = 9
> test_plus3'' = Refl


== Additional Exercises

> namespace Exercises


==== Exercise: 2 stars (fold_length)

Many common functions on lists can be implemented in terms of \idr{fold}. For
example, here is an alternative definition of \idr{length}:

>   fold_length : (l : List x) -> Nat
>   fold_length l = fold (\_, n => S n) l 0

>   test_fold_length1 : fold_length [4,7,0] = 3
>   test_fold_length1 = Refl

Prove the correctness of \idr{fold_length}.

>   fold_length_correct : (l : List x) -> fold_length l = length l
>   fold_length_correct l = ?fold_length_correct_rhs

$\square$


==== Exercise: 3 stars (fold_map)

We can also define \idr{map} in terms of fold. Finish \idr{fold_map} below.

>   fold_map : (f : x -> y) -> (l : List x) -> List y
>   fold_map f l = ?fold_map_rhs

Write down a theorem \idr{fold_map_correct} in Idris stating that \idr{fold_map}
is correct, and prove it.

>   fold_map_correct : ?fold_map_correct

$\square$


==== Exercise: 2 stars, advanced (currying)

In Idris, a function \idr{f: a -> b -> c} really has the type \idr{a -> (b ->
c)}. That is, if you give \idr{f} a value of type \idr{a}, it will give you
function \idr{f' : b -> c}. If you then give \idr{f'} a value of type \idr{b},
it will return a value of type \idr{c}. This allows for partial application, as
in \idr{plus3}. Processing a list of arguments with functions that return
functions is called _currying_, in honor of the logician Haskell Curry.

Conversely, we can reinterpret the type \idr{a -> b -> c} as \idr{(a * b) -> c}.
This is called _uncurrying_. With an uncurried binary function, both arguments
must be given at once as a pair; there is no partial application.

We can define currying as follows:

>   prod_curry : (f : (x * y) -> z) -> (x_val : x) -> (y_val : y) -> z
>   prod_curry f x_val y_val = f (x_val, y_val)

As an exercise, define its inverse, \idr{prod_uncurry}. Then prove the theorems
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
types of \idr{prod_curry} and \idr{prod_uncurry}?

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


==== Exercise: 2 stars, advanced (nth_error_informal)

Recall the definition of the \idr{nth_error} function:

```idris
  nth_error : (l : List x) -> (n : Nat) -> Option x
  nth_error [] n = None
  nth_error (a::l') n = if n == 0
                          then Some a
                          else nth_error l' (pred n)
```

Write an informal proof of the following theorem:

\idr{n -> l -> length l = n -> nth_error l n = None}

> -- FILL IN HERE

$\square$


==== Exercise: 4 stars, advanced (church_numerals)

This exercise explores an alternative way of defining natural numbers, using the
so-called _Church numerals_, named after mathematician Alonzo Church. We can
represent a natural number \idr{n} as a function that takes a function \idr{f}
as a parameter and returns \idr{f} iterated \idr{n} times.

> namespace Church

>   Nat' : {x : Type} -> Type
>   Nat' {x} = (x -> x) -> x -> x

Let's see how to write some numbers with this notation. Iterating a function
once should be the same as just applying it. Thus:

>   one : Nat'
>   one f x = f x

Similarly, \idr{two} should apply \idr{f} twice to its argument:

>   two : Nat'
>   two f x = f (f x)

Defining \idr{zero} is somewhat trickier: how can we "apply a function zero
times"? The answer is actually simple: just return the argument untouched.

>   zero : Nat'
>   zero f x = x

More generally, a number \idr{n} can be written as \idr{\f, x => f (f ... (f x)
...)}, with \idr{n} occurrences of \idr{f}. Notice in particular how the
\idr{doit3times} function we've defined previously is actually just the Church
representation of \idr{3}.

>   three : Nat'
>   three = doit3times

Complete the definitions of the following functions. Make sure that the
corresponding unit tests pass by proving them with \idr{Refl}.

Successor of a natural number:

>   succ' : (n : Nat' {x}) -> Nat' {x}
>   succ' n = ?succ__rhs

When we write a lower case word in an `argument position` Idris assumes it's a
variable even if it shares the name of an earlier definition. To fix this we
prefix \idr{Church} here to make it clear to Idris that they refer to our
earlier definitions.

>   succ'_1 : succ' Church.zero f x = one f x
>   succ'_1 = ?succ__1_rhs

>   succ'_2 : succ' Church.one f x = two f x
>   succ'_2 = ?succ__2_rhs

>   succ'_3 : succ' Church.two f x = three f x
>   succ'_3 = ?succ__3_rhs

Addition of two natural numbers:

>   plus' : (n, m : Nat' {x}) -> Nat' {x}
>   plus' n m = ?plus__rhs

>   plus'_1 : plus' Church.zero Church.one f x = one f x
>   plus'_1 = ?plus__1_rhs

>   plus'_2 : plus' Church.two Church.three = plus' Church.three Church.two
>   plus'_2 = ?plus__2_rhs

>   plus'_3 : plus' (plus' Church.two Church.two) Church.three
>           = plus' Church.one (plus' Church.three Church.three)
>   plus'_3 = ?plus__3_rhs

Multiplication:

>   mult' : (n, m : Nat' {x}) -> Nat' {x}
>   mult' n m = ?mult__rhs

>   mult'_1 : mult' Church.one Church.one f x = one f x
>   mult'_1 = ?mult__1_rhs

>   mult'_2 : mult' Church.zero (plus' Church.three Church.three) f x = zero f x
>   mult'_2 = ?mult__2_rhs

>   mult'_3 : mult' Church.two Church.three = plus' Church.three Church.three
>   mult'_3 = ?mult__3_rhs

Exponentiation:

\todo[inline]{Edit the hint. Can't make it work with \idr{exp' : (n, m : Nat'
{x}) -> Nat' {x}}.}

(Hint: Polymorphism plays a crucial role here. However, choosing the right type
to iterate over can be tricky. If you hit a "Universe inconsistency" error, try
iterating over a different type: \idr{Nat'} itself is usually problematic.)

>   exp' : (n : Nat' {x}) -> (m : Nat' {x=x->x}) -> Nat' {x}
>   exp' n m = ?exp__rhs

>   exp'_1 : exp' Church.two Church.two = plus' Church.two Church.two
>   exp'_1 = ?exp__1_rhs

>   exp'_2 : exp' Church.three Church.two
>          = plus' (mult' Church.two (mult' Church.two Church.two)) Church.one
>   exp'_2 = ?exp__2_rhs

>   exp'_3 : exp' Church.three Church.zero f x = one f x
>   exp'_3 = ?exp__3_rhs

$\square$
