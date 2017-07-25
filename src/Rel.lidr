= Rel : Properties of Relations

> module Rel

This short (and optional) chapter develops some basic definitions and a few
theorems about binary relations in Idris. The key definitions are repeated where
they are actually used (in the `Smallstep` chapter), so readers who are already
comfortable with these ideas can safely skim or skip this chapter. However,
relations are also a good source of exercises for developing facility with
Idris's basic reasoning facilities, so it may be useful to look at this material
just after the `IndProp` chapter.

Require Export IndProp.

A binary _relation_ on a set \idr{t} is a family of propositions parameterized
by two elements of \idr{t} — i.e., a proposition about pairs of elements of
\idr{t}.

> Relation : Type -> Type
> Relation t = t -> t -> Type

\todo[inline]{Edit}

Confusingly, the Idris standard library hijacks the generic term "relation" for
this specific instance of the idea. To maintain consistency with the library, we
will do the same. So, henceforth the Idris identifier `relation` will always
refer to a binary relation between some set and itself, whereas the English word
"relation" can refer either to the specific Idris concept or the more general
concept of a relation between any number of possibly different sets. The context
of the discussion should always make clear which is meant.

\todo[inline]{Called \idr{LTE} in \idr{Prelude.Nat}, but defined via induction
from zero there}

An example relation on \idr{Nat} is \idr{Le}, the less-than-or-equal-to
relation, which we usually write \idr{n1 <= n2}.

\todo[inline]{Copied from `IndProp`}

> data Le : (n : Nat) -> Nat -> Type where
>   Le_n : Le n n
>   Le_S : Le n m -> Le n (S m)
>
> syntax [m] "<='" [n] = Le m n

```idris
λΠ> the (Relation Nat) Le
Le : Nat -> Nat -> Type
```

\todo[inline]{Edit, it probably doesn't matter in Idris}

(Why did we write it this way instead of starting with \idr{data Le : Relation
Nat ...}? Because we wanted to put the first \idr{Nat} to the left of the
\idr{:}, which makes Idris generate a somewhat nicer induction principle for
reasoning about \idr{<='}.)


== Basic Properties

As anyone knows who has taken an undergraduate discrete math course, there is a
lot to be said about relations in general, including ways of classifying
relations (as reflexive, transitive, etc.), theorems that can be proved
generically about certain sorts of relations, constructions that build one
relation from another, etc. For example...


=== Partial Functions

A relation \idr{r} on a set \idr{t} is a partial function if, for every \idr{x},
there is at most one \idr{y} such that \idr{r x y} — i.e., \idr{r x y1} and
\idr{r x y2} together imply \idr{y1 = y2}.

> Partial_function : (r : Relation t) -> Type
> Partial_function {t} r = (x, y1, y2 : t) -> r x y1 -> r x y2 -> y1 = y2

For example, the \idr{Next_nat} relation defined earlier is a partial function.

> data Next_nat : (n : Nat) -> Nat -> Type where
>   NN : Next_nat n (S n)

```idris
λΠ> the (Relation Nat) Next_nat
Next_nat : Nat -> Nat -> Type
```

> next_nat_partial_function : Partial_function Next_nat
> next_nat_partial_function x (S x) (S x) NN NN = Refl

However, the \idr{<='} relation on numbers is not a partial function. (Assume,
for a contradiction, that \idr{<='} is a partial function. But then, since
\idr{0 <=' 0} and \idr{0 <=' 1}, it follows that \idr{0 = 1}. This is nonsense,
so our assumption was contradictory.)

> le_not_a_partial_function : Not (Partial_function Le)
> le_not_a_partial_function f = absurd $ f 0 0 1 Le_n (Le_S Le_n)


==== Exercise: 2 stars, optional

\ \todo[inline]{They mean exercises from `IndProp`}

Show that the idr{Total_relation} defined in earlier is not a partial function.

> -- FILL IN HERE

$\square$


==== Exercise: 2 stars, optional

Show that the idr{Empty_relation} that we defined earlier is a partial function.

> --FILL IN HERE

$\square$


=== Reflexive Relations

A _reflexive_ relation on a set \idr{t} is one for which every element of
\idr{t} is related to itself.

> Reflexive : (r : Relation t) -> Type
> Reflexive {t} r = (a : t) -> r a a

> le_reflexive : Reflexive Le
> le_reflexive n = Le_n {n}


=== Transitive Relations

A relation \idr{r} is _transitive_ if \idr{r a c} holds whenever \idr{r a b} and
\idr{r b c} do.

> Transitive : (r : Relation t) -> Type
> Transitive {t} r = (a, b, c : t) -> r a b -> r b c -> r a c

> le_trans : Transitive Le
> le_trans _ _ _ lab Le_n = lab
> le_trans a b (S c) lab (Le_S lbc) = Le_S $ le_trans a b c lab lbc

\todo[inline]{Copied here}

> Lt : (n, m : Nat) -> Type
> Lt n m = Le (S n) m

> syntax [m] "<'" [n] = Lt m n

> lt_trans : Transitive Lt
> lt_trans a b c lab lbc = le_trans (S a) (S b) c (Le_S lab) lbc


==== Exercise: 2 stars, optional

We can also prove \idr{lt_trans} more laboriously by induction, without using
\idr{le_trans}. Do this.

> lt_trans' : Transitive Lt
> -- Prove this by induction on evidence that a is less than c.
> lt_trans' a b c lab lbc = ?lt_trans'_rhs

$\square$


==== Exercise: 2 stars, optional

Prove the same thing again by induction on \idr{c}.

> lt_trans'' : Transitive Lt
> lt_trans'' a b c lab lbc = ?lt_trans'_rhs

$\square$

The transitivity of \idr{Le}, in turn, can be used to prove some facts that will
be useful later (e.g., for the proof of antisymmetry below)...

> le_Sn_le : ((S n) <=' m) -> (n <=' m)
> le_Sn_le {n} {m} les = le_trans n (S n) m (Le_S Le_n) les


==== Exercise: 1 star, optional

> le_S_n : ((S n) <=' (S m)) -> (n <=' m)
> le_S_n less = ?le_S_n_rhs

$\square$


==== Exercise: 2 stars, optional (le_Sn_n_inf)

Provide an informal proof of the following theorem:

Theorem: For every \idr{n}, \idr{Not ((S n) <=' n)}

A formal proof of this is an optional exercise below, but try writing an
informal proof without doing the formal proof first.

Proof:

> -- FILL IN HERE

$\square$


==== Exercise: 1 star, optional

> le_Sn_n : Not ((S n) <=' n)
> le_Sn_n = ?le_Sn_n_rhs

$\square$

Reflexivity and transitivity are the main concepts we'll need for later
chapters, but, for a bit of additional practice working with relations in Idris,
let's look at a few other common ones...


=== Symmetric and Antisymmetric Relations

A relation \idr{r} is _symmetric_ if \idr{r a b} implies \idr{r b a}.

> Symmetric : (r : Relation t) -> Type
> Symmetric {t} r = (a, b : t) -> r a b -> r b a


==== Exercise: 2 stars, optional

> le_not_symmetric : Not (Symmetric Le)
> le_not_symmetric = ?le_not_symmetric_rhs

$\square$

A relation \idr{r} is _antisymmetric_ if \idr{r a b{} and \idr{r b a} together
imply \idr{a = b} — that is, if the only "cycles" in \idr{r} are trivial ones.

> Antisymmetric : (r : Relation t) -> Type
> Antisymmetric {t} r = (a, b : t) -> r a b -> r b a -> a = b


==== Exercise: 2 stars, optional

> le_antisymmetric : Antisymmetric Le
> le_antisymmetric = ?le_antisymmetric_rhs

$\square$


==== Exercise: 2 stars, optional

> le_step : (n <' m) -> (m <=' (S p)) -> (n <=' p)
> le_step ltnm lemsp = ?le_step_rhs

$\square$


=== Equivalence Relations

A relation is an _equivalence_ if it's reflexive, symmetric, and transitive.

> Equivalence : (r : Relation t) -> Type
> Equivalence r = (Reflexive r, Symmetric r, Transitive r)


=== Partial Orders and Preorders

\ \todo[inline]{Edit}

A relation is a _partial order_ when it's reflexive, _anti_-symmetric, and
transitive. In the Idris standard library it's called just "order" for short.

> Order : (r : Relation t) -> Type
> Order r = (Reflexive r, Antisymmetric r, Transitive r)

A preorder is almost like a partial order, but doesn't have to be antisymmetric.

> Preorder : (r : Relation t) -> Type
> Preorder r = (Reflexive r, Transitive r)

> le_order : Order Le
> le_order = (le_reflexive, le_antisymmetric, le_trans)


== Reflexive, Transitive Closure

\ \todo[inline]{Edit}

The _reflexive, transitive closure_ of a relation \idr{r} is the smallest
relation that contains \idr{r} and that is both reflexive and transitive.
Formally, it is defined like this in the Relations module of the Idris standard
library:

> data Clos_refl_trans : (r : Relation t) -> Relation t where
>   Rt_step : r x y -> Clos_refl_trans r x y
>   Rt_refl : Clos_refl_trans r x x
>   Rt_trans : Clos_refl_trans r x y -> Clos_refl_trans r y z ->
>              Clos_refl_trans r x z

For example, the reflexive and transitive closure of the \idr{Next_nat} relation
coincides with the \idr{Le} relation.

\todo[inline]{Copied `<->` for now}

> iff : {p,q : Type} -> Type
> iff {p} {q} = (p -> q, q -> p)
>
> syntax [p] "<->" [q] = iff {p} {q}

> next_nat_closure_is_le : (n <=' m) <-> (Clos_refl_trans Next_nat n m)
> next_nat_closure_is_le = (to, fro)
>   where
>     to : Le n m -> Clos_refl_trans Next_nat n m
>     to Le_n = Rt_refl
>     to (Le_S {m} le) = Rt_trans {y=m} (to le) (Rt_step NN)
>     fro : Clos_refl_trans Next_nat n m -> Le n m
>     fro (Rt_step NN) = Le_S Le_n
>     fro Rt_refl = Le_n
>     fro (Rt_trans {x=n} {y} {z=m} ny ym) =
>       le_trans n y m (fro ny) (fro ym)

The above definition of reflexive, transitive closure is natural: it says,
explicitly, that the reflexive and transitive closure of \idr{r} is the least
relation that includes \idr{r} and that is closed under rules of reflexivity and
transitivity. But it turns out that this definition is not very convenient for
doing proofs, since the "nondeterminism" of the \idr{Rt_trans} rule can
sometimes lead to tricky inductions. Here is a more useful definition:

> data Clos_refl_trans_1n : (r : Relation t) -> (x : t) -> t -> Type where
>   Rt1n_refl : Clos_refl_trans_1n r x x
>   Rt1n_trans : r x y -> Clos_refl_trans_1n r y z -> Clos_refl_trans_1n r x z

\todo[inline]{Edit}

Our new definition of reflexive, transitive closure "bundles" the \idr{Rt_step}
and \idr{Rt_trans} rules into the single rule step. The left-hand premise of
this step is a single use of \idr{r}, leading to a much simpler induction
principle.

Before we go on, we should check that the two definitions do indeed define the
same relation...

First, we prove two lemmas showing that \idr{Clos_refl_trans_1n} mimics the
behavior of the two "missing" \idr{Clos_refl_trans} constructors.

> rsc_R : r x y -> Clos_refl_trans_1n r x y
> rsc_R rxy = Rt1n_trans rxy Rt1n_refl


==== Exercise: 2 stars, optional (rsc_trans)

> rsc_trans : Clos_refl_trans_1n r x y -> Clos_refl_trans_1n r y z ->
>             Clos_refl_trans_1n r x z
> rsc_trans crxy cryz = ?rsc_trans_rhs

$\square$

Then we use these facts to prove that the two definitions of reflexive, transitive closure do indeed define the same relation.


==== Exercise: 3 stars, optional (rtc_rsc_coincide)

> rtc_rsc_coincide : (Clos_refl_trans r x y) <-> (Clos_refl_trans_1n r x y)
> rtc_rsc_coincide = ?rtc_rsc_coincide_rhs

$\square$
