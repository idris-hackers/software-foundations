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
> le_not_a_partial_function f = ?le_not_a_partial_function_rhs


==== Exercise: 2 stars, optional

Show that the total_relation defined in earlier is not a partial function.

(* FILL IN HERE *)

$\square$


==== Exercise: 2 stars, optional

Show that the empty_relation that we defined earlier is a partial function.

(* FILL IN HERE *)

$\square$


=== Reflexive Relations

A reflexive relation on a set X is one for which every element of X is related
to itself.

Definition reflexive {X: Type} (R: relation X) :=
  ∀a : X, R a a.

Theorem le_reflexive :
  reflexive le.


=== Transitive Relations

A relation R is transitive if R a c holds whenever R a b and R b c do.

Definition transitive {X: Type} (R: relation X) :=
  ∀a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.

Theorem lt_trans:
  transitive lt.


==== Exercise: 2 stars, optional

We can also prove lt_trans more laboriously by induction, without using
le_trans. Do this.

Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that m is less than o. *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
    (* FILL IN HERE *) Admitted.

$\square$


==== Exercise: 2 stars, optional

Prove the same thing again by induction on o.

Theorem lt_trans'' :
  transitive lt.

$\square$

The transitivity of le, in turn, can be used to prove some facts that will be
useful later (e.g., for the proof of antisymmetry below)...

Theorem le_Sn_le : ∀n m, S n ≤ m -> n ≤ m.

==== Exercise: 1 star, optional

Theorem le_S_n : ∀n m,
  (S n ≤ S m) -> (n ≤ m).
Proof.
  (* FILL IN HERE *) Admitted.

$\square$


==== Exercise: 2 stars, optional (le_Sn_n_inf)

Provide an informal proof of the following theorem:

Theorem: For every n, ¬ (S n ≤ n)

A formal proof of this is an optional exercise below, but try writing an
informal proof without doing the formal proof first.

Proof: (* FILL IN HERE *)

$\square$


==== Exercise: 1 star, optional

Theorem le_Sn_n : ∀n,
  ¬ (S n ≤ n).
Proof.
  (* FILL IN HERE *) Admitted.

$\square$

Reflexivity and transitivity are the main concepts we'll need for later
chapters, but, for a bit of additional practice working with relations in Idris,
let's look at a few other common ones...


=== Symmetric and Antisymmetric Relations

A relation R is symmetric if R a b implies R b a.

Definition symmetric {X: Type} (R: relation X) :=
  ∀a b : X, (R a b) -> (R b a).


==== Exercise: 2 stars, optional

Theorem le_not_symmetric :
  ¬ (symmetric le).
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
A relation R is antisymmetric if R a b and R b a together imply a = b — that is, if the only "cycles" in R are trivial ones.

Definition antisymmetric {X: Type} (R: relation X) :=
  ∀a b : X, (R a b) -> (R b a) -> a = b.


==== Exercise: 2 stars, optional

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$


==== Exercise: 2 stars, optional

Theorem le_step : ∀n m p,
  n < m ->
  m ≤ S p ->
  n ≤ p.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$


=== Equivalence Relations

A relation is an equivalence if it's reflexive, symmetric, and transitive.

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) ∧ (symmetric R) ∧ (transitive R).


=== Partial Orders and Preorders

A relation is a partial order when it's reflexive, anti-symmetric, and
transitive. In the Idris standard library it's called just "order" for short.

Definition order {X:Type} (R: relation X) :=
  (reflexive R) ∧ (antisymmetric R) ∧ (transitive R).

A preorder is almost like a partial order, but doesn't have to be antisymmetric.

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) ∧ (transitive R).

Theorem le_order :
  order le.


== Reflexive, Transitive Closure

The reflexive, transitive closure of a relation R is the smallest relation that
contains R and that is both reflexive and transitive. Formally, it is defined
like this in the Relations module of the Idris standard library:

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step : ∀x y, R x y -> clos_refl_trans R x y
    | rt_refl : ∀x, clos_refl_trans R x x
    | rt_trans : ∀x y z,
          clos_refl_trans R x y ->
          clos_refl_trans R y z ->
          clos_refl_trans R x z.

For example, the reflexive and transitive closure of the next_nat relation
coincides with the le relation.

Theorem next_nat_closure_is_le : ∀n m,
  (n ≤ m) <-> ((clos_refl_trans next_nat) n m).

The above definition of reflexive, transitive closure is natural: it says,
explicitly, that the reflexive and transitive closure of R is the least relation
that includes R and that is closed under rules of reflexivity and transitivity.
But it turns out that this definition is not very convenient for doing proofs,
since the "nondeterminism" of the rt_trans rule can sometimes lead to tricky
inductions. Here is a more useful definition:

Inductive clos_refl_trans_1n {A : Type}
                             (R : relation A) (x : A)
                             : A -> Type :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A) :
      R x y -> clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.

Our new definition of reflexive, transitive closure "bundles" the rt_step and
rt_trans rules into the single rule step. The left-hand premise of this step is
a single use of R, leading to a much simpler induction principle.

Before we go on, we should check that the two definitions do indeed define the
same relation...

First, we prove two lemmas showing that clos_refl_trans_1n mimics the behavior
of the two "missing" clos_refl_trans constructors.

Lemma rsc_R : ∀(X:Type) (R:relation X) (x y : X),
       R x y -> clos_refl_trans_1n R x y.


==== Exercise: 2 stars, optional (rsc_trans)

Lemma rsc_trans :
  ∀(X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$

Then we use these facts to prove that the two definitions of reflexive, transitive closure do indeed define the same relation.


==== Exercise: 3 stars, optional (rtc_rsc_coincide)

Theorem rtc_rsc_coincide :
         ∀(X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> clos_refl_trans_1n R x y.
Proof.
  (* FILL IN HERE *) Admitted.

$\square$
