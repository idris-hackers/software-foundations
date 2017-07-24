= IndProp: Inductively Defined Propositions

> module IndProp
>
> import Basics
> import Induction
>
> %hide Basics.Numbers.pred
> %hide Prelude.Stream.(::)
>

== Inductively Defined Propositions

In the `Logic` chapter, we looked at several ways of writing propositions,
including conjunction, disjunction, and quantifiers. In this chapter, we bring a
new tool into the mix: _inductive definitions_.

Recall that we have seen two ways of stating that a number \idr{n} is even: We
can say (1) \idr{evenb n = True}, or (2) \idr{(k ** n = double k)}. Yet another
possibility is to say that \idr{n} is even if we can establish its evenness from
the following rules:

  - Rule \idr{ev_0}: The number \idr{0} is even.
  - Rule \idr{ev_SS}: If \idr{n} is even, then \idr{S (S n)} is even.

To illustrate how this definition of evenness works, let's imagine using it to
show that \idr{4} is even. By rule \idr{ev_SS}, it suffices to show that \idr{2}
is even. This, in turn, is again guaranteed by rule \idr{ev_SS}, as long as we
can show that \idr{0} is even. But this last fact follows directly from the
\idr{ev_0} rule.

We will see many definitions like this one during the rest of the course. For
purposes of informal discussions, it is helpful to have a lightweight notation
that makes them easy to read and write. _Inference rules_ are one such notation:

\todo[inline]{Use proper TeX}

```
                                   ---- (ev_0)
                                   ev 0	

                                   ev n	
                               ------------ (ev_SS)
                               ev (S (S n))	
```

Each of the textual rules above is reformatted here as an inference rule; the
intended reading is that, if the _premises_ above the line all hold, then the
conclusion below the line follows. For example, the rule \idr{ev_SS} says that,
if \idr{n} satisfies \idr{ev}, then \idr{S (S n)} also does. If a rule has no
premises above the line, then its conclusion holds unconditionally.

We can represent a proof using these rules by combining rule applications into a
_proof tree_. Here's how we might transcribe the above proof that \idr{4} is
even:

```
                             ------  (ev_0)
                              ev 0
                             ------ (ev_SS)
                              ev 2
                             ------ (ev_SS)
                              ev 4
```

Why call this a "tree" (rather than a "stack", for example)? Because, in
general, inference rules can have multiple premises. We will see examples of
this below.

Putting all of this together, we can translate the definition of evenness into a
formal Idris definition using an \idr{data} declaration, where each constructor
corresponds to an inference rule:

> data Ev : Nat -> Type where
>   Ev_0 : Ev Z
>   Ev_SS : {n : Nat} -> Ev n -> Ev (S (S n))
>

This definition is different in one crucial respect from previous uses of
\idr{data}: its result is not a \idr{Type}, but rather a function from \idr{Nat}
to \idr{Type} -- that is, a property of numbers. Note that we've already seen
other inductive definitions that result in functions, such as \idr{List}, whose
type is \idr{Type -> Type}. What is new here is that, because the \idr{Nat}
argument of \idr{Ev} appears unnamed, to the right of the colon, it is allowed
to take different values in the types of different constructors: \idr{Z} in the
type of \idr{Ev_0} and \idr{S (S n)} in the type of \idr{Ev_SS}.

In contrast, the definition of \idr{List} names the \idr{x} parameter globally,
forcing the result of \idr{Nil} and \idr{(::)} to be the same (\idr{List x}).
Had we tried to name \idr{Nat} in defining \idr{Ev}, we would have seen an
error:

```idris
data Wrong_ev : (n : Nat) -> Type where
  Wrong_ev_0 : Wrong_ev Z
  Wrong_ev_SS : n -> Wrong_ev n -> Wrong_ev (S (S n))
```

```idris
When checking type of IndType.Wrong_ev_SS:
When checking argument n to IndType.Wrong_ev:
        Type mismatch between
                Type (Type of n)
        and
                Nat (Expected type)
```

\todo[inline]{Edit the explanation, it works fine if you remove the first \idr{n ->}
in \idr{Wrong_ev_SS}}

("Parameter" here is Idris jargon for an argument on the left of the colon in an
Inductive definition; "index" is used to refer to arguments on the right of the
colon.)

We can think of the definition of \idr{Ev} as defining a Idris property
\idr{Ev : Nat -> Type}, together with theorems \idr{Ev_0 : Ev Z} and
\idr{Ev_SS : n -> Ev n -> Ev (S (S n))}. Such "constructor theorems" have the
same status as proven theorems. In particular, we can apply rule names as
functions to each other to prove \idr{Ev} for particular numbers...

> ev_4 : Ev 4
> ev_4 = Ev_SS {n=2} $ Ev_SS {n=0} Ev_0
>

We can also prove theorems that have hypotheses involving \idr{Ev}.

> ev_plus4 : Ev n -> Ev (4 + n)
> ev_plus4 x = Ev_SS $ Ev_SS x
>

More generally, we can show that any number multiplied by 2 is even:


==== Exercise: 1 star (ev_double)

> ev_double : Ev (double n)
> ev_double = ?ev_double_rhs
>

$\square$


== Using Evidence in Proofs

Besides _constructing_ evidence that numbers are even, we can also _reason
about_ such evidence.

Introducing \idr{Ev} with a \idr{data} declaration tells Idris not only that the
constructors \idr{Ev_0} and \idr{Ev_SS} are valid ways to build evidence that
some number is even, but also that these two constructors are the _only_ ways to
build evidence that numbers are even (in the sense of \idr{Ev}).

In other words, if someone gives us evidence \idr{e} for the assertion \idr{Ev
n}, then we know that \idr{e} must have one of two shapes:

  - \idr{e} is \idr{Ev_0} (and \idr{n} is \idr{Z}), or

  - \idr{e} is \idr{Ev_SS {n=n'} e'} (and \idr{n} is \idr{S (S n')}, where
    \idr{e'} is evidence for \idr{Ev n'}).

This suggests that it should be possible to analyze a hypothesis of the form
\idr{Ev n} much as we do inductively defined data structures; in particular, it
should be possible to argue by _induction_ and _case analysis_ on such evidence.
Let's look at a few examples to see what this means in practice.


=== Pattern Matching on Evidence

\ \todo[inline]{Edit the whole section to talk about dependent pattern matching}

Suppose we are proving some fact involving a number \idr{n}, and we are given
\idr{Ev n} as a hypothesis. We already know how to perform case analysis on
\idr{n} using the `inversion` tactic, generating separate subgoals for the case
where \idr{n = Z} and the case where \idr{n = S n'} for some \idr{n'}. But for
some proofs we may instead want to analyze the evidence that \idr{Ev n}
directly.

By the definition of \idr{Ev}, there are two cases to consider:

  - If the evidence is of the form \idr{Ev_0}, we know that \idr{n = Z}.

  - Otherwise, the evidence must have the form \idr{Ev_SS {n=n'} e'}, where
    \idr{n = S (S n')} and \idr{e'} is evidence for \idr{Ev n'}.

We can perform this kind of reasoning in Idris, again using pattern matching.
Besides allowing us to reason about equalities involving constructors,
`inversion` provides a case-analysis principle for inductively defined
propositions. When used in this way, its syntax is similar to `destruct`: We
pass it a list of identifiers separated by `|` characters to name the arguments
to each of the possible constructors.

> ev_minus2 : Ev n -> Ev (pred (pred n))
> ev_minus2 Ev_0       = Ev_0
> ev_minus2 (Ev_SS e') = e'
>

In words, here is how the pattern match reasoning works in this proof:

  - If the evidence is of the form \idr{Ev_0}, we know that \idr{n = Z}.
    Therefore, it suffices to show that \idr{Ev (pred (pred Z))} holds. By the
    definition of \idr{pred}, this is equivalent to showing that \idr{Ev Z}
    holds, which directly follows from \idr{Ev_0}.

  - Otherwise, the evidence must have the form \idr{Ev_SS {n=n'} e'}, where
    \idr{n = S (S n')} and \idr{e'} is evidence for \idr{Ev n'}. We must then
    show that \idr{Ev (pred (pred (S (S n'))))} holds, which, after
    simplification, follows directly from \idr{e'}.

Suppose that we wanted to prove the following variation of \idr{ev_minus2}:

> evSS_ev : Ev (S (S n)) -> Ev n

Intuitively, we know that evidence for the hypothesis cannot consist just of the
\idr{Ev_0} constructor, since \idr{Z} and \idr{S} are different constructors of
the type \idr{Nat}; hence, \idr{Ev_SS} is the only case that applies.
Unfortunately, destruct is not smart enough to realize this, and it still
generates two subgoals. Even worse, in doing so, it keeps the final goal
unchanged, failing to provide any useful information for completing the proof.

The inversion tactic, on the other hand, can detect (1) that the first case does
not apply, and (2) that the \idr{n'} that appears on the \idr{Ev_SS} case must be the
same as \idr{n}. This allows us to complete the proof

> evSS_ev (Ev_SS e') = e'
>

By using dependent pattern matching, we can also apply the principle of
explosion to "obviously contradictory" hypotheses involving inductive
properties. For example:

> one_not_even : Not (Ev 1)
> one_not_even Ev_0 impossible
> one_not_even (Ev_SS _) impossible
>


=== Exercise: 1 star (inversion_practice)

Prove the following results using pattern matching.

> SSSSev__even : Ev (S (S (S (S n)))) -> Ev n
> SSSSev__even e = ?SSSSev__even_rhs
>
> even5_nonsense : Ev 5 -> 2 + 2 = 9
> even5_nonsense e = ?even5_nonsense_rhs
>

$\square$

\todo[inline]{Edit}

The way we've used `inversion` here may seem a bit mysterious at first. Until now,
we've only used `inversion` on equality propositions, to utilize injectivity of
constructors or to discriminate between different constructors. But we see here
that `inversion` can also be applied to analyzing evidence for inductively defined
propositions.

Here's how `inversion` works in general. Suppose the name `I` refers to an
assumption `P` in the current context, where `P` has been defined by an
`Inductive` declaration. Then, for each of the constructors of `P`, `inversion
I` generates a subgoal in which `I` has been replaced by the exact, specific
conditions under which this constructor could have been used to prove `P`. Some
of these subgoals will be self-contradictory; `inversion` throws these away. The
ones that are left represent the cases that must be proved to establish the
original goal. For those, `inversion` adds all equations into the proof context
that must hold of the arguments given to `P` (e.g., \idr{S (S n') = n} in the
proof of \idr{evSS_ev}).

The \idr{ev_double} exercise above shows that our new notion of evenness is
implied by the two earlier ones (since, by \idr{even_bool_prop} in chapter
`Logic`, we already know that those are equivalent to each other). To show that
all three coincide, we just need the following lemma:

> ev_even : Ev n -> (k ** n = double k)

We proceed by case analysis on \idr{Ev n}. The first case can be solved
trivially.

> ev_even Ev_0 = (Z ** Refl)

Unfortunately, the second case is harder. We need to show \idr{(k ** S (S n') =
double k}, but the only available assumption is \idr{e'}, which states that
\idr{Ev n'} holds. Since this isn't directly useful, it seems that we are stuck
and that performing case analysis on \idr{Ev n} was a waste of time.

If we look more closely at our second goal, however, we can see that something
interesting happened: By performing case analysis on \idr{Ev n}, we were able to
reduce the original result to an similar one that involves a _different_ piece
of evidence for \idr{Ev n}: \idr{e'}. More formally, we can finish our proof by
showing that

```idris
(k' ** n' = double k')
```

which is the same as the original statement, but with \idr{n'} instead of
\idr{n}. Indeed, it is not difficult to convince Idris that this intermediate
result suffices.

> ev_even (Ev_SS e') = I $ ev_even e'
>   where
>     I : (k' ** n' = double k') -> (k ** S (S n') = double k)
>     I (k' ** prf) = (S k' ** cong {f=S} $ cong {f=S} prf)
>


=== Induction on Evidence

\ \todo[inline]{Edit, we've already just done an induction-style proof, the
following is basically replacing `where` with `let`}

If this looks familiar, it is no coincidence: We've encountered similar problems
in the `Induction` chapter, when trying to use case analysis to prove results
that required induction. And once again the solution is... induction!

The behavior of `induction` on evidence is the same as its behavior on data: It
causes Idris to generate one subgoal for each constructor that could have used
to build that evidence, while providing an induction hypotheses for each
recursive occurrence of the property in question.

Let's try our current lemma again:

> ev_even' : Ev n -> (k ** n = double k)
> ev_even' Ev_0 = (Z ** Refl)
> ev_even' (Ev_SS e') = let
>   (k**prf) = ev_even e'
>   cprf = cong {f=S} $ cong {f=S} prf
> in
>   rewrite cprf in (S k ** Refl)

Here, we can see that Idris produced an `IH` that corresponds to `E'`, the single
recursive occurrence of ev in its own definition. Since E' mentions n', the
induction hypothesis talks about n', as opposed to n or some other number.

The equivalence between the second and third definitions of evenness now
follows.

\todo[inline]{Copypasted `<->` for now}

> iff : {p,q : Type} -> Type
> iff {p} {q} = (p -> q, q -> p)
>
> syntax [p] "<->" [q] = iff {p} {q}
>
> ev_even_iff : (Ev n) <-> (k ** n = double k)
> ev_even_iff = (ev_even, fro)
>   where
>     fro : (k ** n = double k) -> (Ev n)
>     fro (k ** prf) = rewrite prf in ev_double {n=k}
>

As we will see in later chapters, induction on evidence is a recurring technique
across many areas, and in particular when formalizing the semantics of
programming languages, where many properties of interest are defined
inductively.

The following exercises provide simple examples of this technique, to help you
familiarize yourself with it.


==== Exercise: 2 stars (ev_sum)

> ev_sum : Ev n -> Ev m -> Ev (n + m)
> ev_sum x y = ?ev_sum_rhs
>

$\square$


=== Exercise: 4 stars, advanced, optional (ev_alternate)

In general, there may be multiple ways of defining a property inductively. For
example, here's a (slightly contrived) alternative definition for \idr{Ev}:

> data Ev' : Nat -> Type where
>   Ev'_0 : Ev' Z
>   Ev'_2 : Ev' 2
>   Ev'_sum : Ev' n -> Ev' m -> Ev' (n + m)
>

Prove that this definition is logically equivalent to the old one. (You may want
to look at the previous theorem when you get to the induction step.)

> ev'_ev : (Ev' n) <-> Ev n
> ev'_ev = ?ev'_ev_rhs
>

$\square$


=== Exercise: 3 stars, advanced, recommended (ev_ev__ev)

Finding the appropriate thing to do induction on is a bit tricky here:

> ev_ev__ev : Ev (n+m) -> Ev n -> Ev m
> ev_ev__ev x y = ?ev_ev__ev_rhs
>

$\square$


==== Exercise: 3 stars, optional (ev_plus_plus)

This exercise just requires applying existing lemmas. No induction or even case
analysis is needed, though some of the rewriting may be tedious.

> ev_plus_plus : Ev (n+m) -> Ev (n+p) -> Ev (m+p)
> ev_plus_plus x y = ?ev_plus_plus_rhs
>

$\square$


== Inductive Relations

A proposition parameterized by a number (such as \idr{Ev}) can be thought of as
a _property_ -- i.e., it defines a subset of \idr{Nat}, namely those numbers for
which the proposition is provable. In the same way, a two-argument proposition
can be thought of as a _relation_ -- i.e., it defines a set of pairs for which
the proposition is provable.

One useful example is the "less than or equal to" relation on numbers.

The following definition should be fairly intuitive. It says that there are two
ways to give evidence that one number is less than or equal to another: either
observe that they are the same number, or give evidence that the first is less
than or equal to the predecessor of the second.

> data Le : Nat -> Nat -> Type where
>   Le_n : Le n n
>   Le_S : Le n m -> Le n (S m)
>
> syntax [m] "<='" [n] = Le m n
>

Proofs of facts about \idr{<='} using the constructors \idr{Le_n} and \idr{Le_S}
follow the same patterns as proofs about properties, like \idr{Ev} above. We can
apply the constructors to prove \idr{<='} goals (e.g., to show that \idr{3<='3}
or \idr{3<='6}), and we can use pattern matching to extract information from
\idr{<='} hypotheses in the context (e.g., to prove that \idr{(2<='1) ->
2+2=5}.)

Here are some sanity checks on the definition. (Notice that, although these are
the same kind of simple "unit tests" as we gave for the testing functions we
wrote in the first few lectures, we must construct their proofs explicitly --
\idr{Refl} doesn't do the job, because the proofs aren't just a matter of
simplifying computations.)

> test_le1 : 3 <=' 3
> test_le1 = Le_n
>
> test_le2 : 3 <=' 6
> test_le2 = Le_S $ Le_S $ Le_S Le_n
>
> test_le3 : (2<='1) -> 2+2=5
> test_le3 (Le_S Le_n) impossible
> test_le3 (Le_S (Le_S _)) impossible
>

The "strictly less than" relation \idr{n < m} can now be defined in terms of
\idr{Le}.

> Lt : (n, m : Nat) -> Type
> Lt n m = Le (S n) m
>
> syntax [m] "<'" [n] = Lt m n
>

Here are a few more simple relations on numbers:

> data Square_of : Nat -> Nat -> Type where
>   Sq : Square_of n (n * n)
>
> data Next_nat : Nat -> Nat -> Type where
>   Nn : Next_nat n (S n)
>
> data Next_even : Nat -> Nat -> Type where
>   Ne_1 : Ev (S n) -> Next_even n (S n)
>   Ne_2 : Ev (S (S n)) -> Next_even n (S (S n))


==== Exercise: 2 stars, optional (total_relation)

Define an inductive binary relation \idr{Total_relation} that holds between
every pair of natural numbers.

> -- FILL IN HERE
>

$\square$


=== Exercise: 2 stars, optional (empty_relation)

Define an inductive binary relation \idr{Empty_relation} (on numbers) that never
holds.

> --FILL IN HERE
>

$\square$


==== Exercise: 3 stars, optional (le_exercises)

Here are a number of facts about the \idr{<='} and \idr{<'} relations that we
are going to need later in the course. The proofs make good practice exercises.

> le_trans : (m <=' n) -> (n <=' o) -> (m <=' o)
> le_trans x y = ?le_trans_rhs
>
> O_le_n : Z <=' n
> O_le_n = ?O_le_n_rhs
>
> n_le_m__Sn_le_Sm : (n <=' m) -> ((S n) <=' (S m))
> n_le_m__Sn_le_Sm x = ?n_le_m__Sn_le_Sm_rhs
>
> Sn_le_Sm__n_le_m : ((S n) <=' (S m)) -> (n <=' m)
> Sn_le_Sm__n_le_m x = ?Sn_le_Sm__n_le_m_rhs
>
> le_plus_l : a <=' (a + b)
> le_plus_l = ?le_plus_l_rhs
>
> plus_lt : ((n1 + n2) <' m) -> (n1 <' m, n2 <' m)
> plus_lt x = ?plus_lt_rhs
>
> lt_S : (n <' m) -> (n <' S m)
> lt_S x = ?lt_S_rhs
>
> leb_complete : leb n m = True -> (n <=' m)
> leb_complete prf = ?leb_complete_rhs
>

Hint: The next one may be easiest to prove by induction on \idr{m}.

> leb_correct : (n <=' m) -> leb n m = True
> leb_correct x = ?leb_correct_rhs
>

Hint: This theorem can easily be proved without using induction.

> leb_true_trans : leb n m = True -> leb m o = True -> leb n o = True
> leb_true_trans prf prf1 = ?leb_true_trans_rhs
>


==== Exercise: 2 stars, optional (leb_iff)

> leb_iff : (leb n m = True) <-> (n <=' m)
> leb_iff = ?leb_iff_rhs
>

$\square$

> namespace R
>

==== Exercise: 3 stars, recommendedM (R_provability)

We can define three-place relations, four-place relations, etc., in just the
same way as binary relations. For example, consider the following three-place
relation on numbers:

>   data R : Nat -> Nat -> Nat -> Type where
>     C1 : R 0 0 0
>     C2 : R m n o -> R (S m) n (S o)
>     C3 : R m n o -> R m (S n) (S o)
>     C4 : R (S m) (S n) (S (S o)) -> R m n o
>     C5 : R m n o -> R n m o
>

Which of the following propositions are provable?

  - \idr{R 1 1 2}

  - \idr{R 2 2 6}

  - If we dropped constructor \idr{C5} from the definition of \idr{R}, would the
    set of provable propositions change? Briefly (1 sentence) explain your
    answer.

  - If we dropped constructor \idr{C4} from the definition of \idr{R}, would the
    set of provable propositions change? Briefly (1 sentence) explain your
    answer.

> -- FILL IN HERE
>

$\square$


==== Exercise: 3 stars, optional (R_fact)

The relation \idr{R} above actually encodes a familiar function. Figure out
which function; then state and prove this equivalence in Idris?

>   fR : Nat -> Nat -> Nat
>   fR k j = ?fR_rhs
>
>   R_equiv_fR : (R m n o) <-> (fR m n = o)
>   R_equiv_fR = ?R_equiv_fR_rhs
>

$\square$


=== Exercise: 4 stars, advanced (subsequence)

A list is a _subsequence_ of another list if all of the elements in the first
list occur in the same order in the second list, possibly with some extra
elements in between. For example,

```idris
      [1,2,3]
```

is a subsequence of each of the lists

```idris
      [1,2,3]
      [1,1,1,2,2,3]
      [1,2,7,3]
      [5,6,1,9,9,2,7,3,8]
```

but it is not a subsequence of any of the lists

```idris
      [1,2]
      [1,3]
      [5,6,2,1,7,3,8]
```

  - Define an inductive type \idr{Subseq} on \idr{List Nat} that captures what
    it means to be a subsequence. (Hint: You'll need three cases.)

  - Prove \idr{subseq_refl} that subsequence is reflexive, that is, any list is
    a subsequence of itself.

  - Prove \idr{subseq_app} that for any lists \idr{l1}, \idr{l2}, and \idr{l3},
    if \idr{l1} is a subsequence of \idr{l2}, then \idr{l1} is also a
    subsequence of \idr{l2 ++ l3}.

  - (Optional, harder) Prove \idr{subseq_trans} that subsequence is transitive
    -- that is, if \idr{l1} is a subsequence of \idr{l2} and \idr{l2} is a
    subsequence of \idr{l3}, then \idr{l1} is a subsequence of \idr{l3}. Hint:
    choose your induction carefully!

> -- FILL IN HERE

$\square$


==== Exercise: 2 stars, optionalM (R_provability2)

Suppose we give Idris the following definition:

>   data R' : Nat -> List Nat -> Type where
>     C1' : R' 0 []
>     C2' : R' n l -> R' (S n) (n :: l)
>     C3' : R' (S n) l -> R' n l
>

Which of the following propositions are provable?

  - \idr{R' 2 [1,0]}

  - \idr{R' 1 [1,2,1,0]}

  - \idr{R' 6 [3,2,1,0]}

$\square$


== Case Study: Regular Expressions

The \idr{Ev} property provides a simple example for illustrating inductive
definitions and the basic techniques for reasoning about them, but it is not
terribly exciting -- after all, it is equivalent to the two non-inductive of
evenness that we had already seen, and does not seem to offer any concrete
benefit over them. To give a better sense of the power of inductive definitions,
we now show how to use them to model a classic concept in computer science:
_regular expressions_.

Regular expressions are a simple language for describing strings, defined as
follows:

> data Reg_exp : (t : Type) -> Type where
>   EmptySet : Reg_exp t
>   EmptyStr : Reg_exp t
>   Chr : t -> Reg_exp t
>   App : Reg_exp t -> Reg_exp t -> Reg_exp t
>   Union : Reg_exp t -> Reg_exp t -> Reg_exp t
>   Star : Reg_exp t -> Reg_exp t
>

Note that this definition is _polymorphic_: Regular expressions in \idr{Reg_exp
t} describe strings with characters drawn from\idr{t} -- that is, lists of
elements of \idr{t}.

(We depart slightly from standard practice in that we do not require the type
\idr{t} to be finite. This results in a somewhat different theory of regular
expressions, but the difference is not significant for our purposes.)

We connect regular expressions and strings via the following rules, which define
when a regular expression _matches_ some string:

  - The expression \idr{EmptySet} does not match any string.

  - The expression \idr{EmptyStr} matches the empty string \idr{[]}.

  - The expression \idr{Chr x} matches the one-character string \idr{[x]}.

  - If \idr{re1} matches \idr{s1}, and \idr{re2} matches \idr{s2}, then \idr{App
    re1 re2} matches \idr{s1 ++ s2}.

  - If at least one of \idr{re1} and \idr{re2} matches \idr{s}, then \idr{Union
    re1 re2} matches \idr{s}.

  - Finally, if we can write some string \idr{s} as the concatenation of a
    sequence of strings \idr{s = s_1 ++ ... ++ s_k}, and the expression \idr{re}
    matches each one of the strings \idr{s_i}, then \idr{Star re} matches
    \idr{s}.

    As a special case, the sequence of strings may be empty, so \idr{Star re}
    always matches the empty string \idr{[]} no matter what \idr{re} is.

We can easily translate this informal definition into a \idr{data} one as
follows:

> data Exp_match : List t -> Reg_exp t -> Type where
>   MEmpty : Exp_match [] EmptyStr
>   MChar : Exp_match [x] (Chr x)
>   MApp : Exp_match s1 re1 -> Exp_match s2 re2 ->
>          Exp_match (s1 ++ s2) (App re1 re2)
>   MUnionL : Exp_match s1 re1 ->
>             Exp_match s1 (Union re1 re2)
>   MUnionR : Exp_match s2 re2 ->
>             Exp_match s2 (Union re1 re2)
>   MStar0 : Exp_match [] (Star re)
>   MStarApp : Exp_match s1 re ->
>              Exp_match s2 (Star re) ->
>              Exp_match (s1 ++ s2) (Star re)
>

Again, for readability, we can also display this definition using inference-rule
notation. At the same time, let's introduce a more readable infix notation.

> syntax [s] "=~" [re] = (Exp_match s re)
>

\todo[inline]{Use proper TeX?}

```idris
                                     -------------- (MEmpty)
                                     [] =~ EmptyStr

                                     ------------ (MChar)
                                     [x] =~ Chr x

                               s1 =~ re1    s2 =~ re2	
                              ----------------------- (MApp)
                              s1 ++ s2 =~ App re1 re2	

                                       s1 =~ re1	
                                 ------------------- (MUnionL)
                                 s1 =~ Union re1 re2

                                       s2 =~ re2	
                                 ------------------- (MUnionR)
                                 s2 =~ Union re1 re2	

                                    ------------- (MStar0)
                                    [] =~ Star re	

                             s1 =~ re    s2 =~ Star re
                             ------------------------- (MStarApp)
                                s1 ++ s2 =~ Star re	
```

Notice that these rules are not _quite_ the same as the informal ones that we
gave at the beginning of the section. First, we don't need to include a rule
explicitly stating that no string matches \idr{EmptySet}; we just don't happen
to include any rule that would have the effect of some string matching
\idr{EmptySet}. (Indeed, the syntax of inductive definitions doesn't even
_allow_ us to give such a "negative rule.")

Second, the informal rules for \idr{Union} and \idr{Star} correspond to two
constructors each: \idr{MUnionL} / \idr{MUnionR}, and \idr{MStar0} /
\idr{MStarApp}. The result is logically equivalent to the original rules but
more convenient to use in Idris, since the recursive occurrences of
\idr{Exp_match} are given as direct arguments to the constructors, making it
easier to perform induction on evidence. (The \idr{exp_match_ex1} and
\idr{exp_match_ex2} exercises below ask you to prove that the constructors given
in the inductive declaration and the ones that would arise from a more literal
transcription of the informal rules are indeed equivalent.)

Let's illustrate these rules with a few examples.

> reg_exp_ex1 : [1] =~ (Chr 1)
> reg_exp_ex1 = MChar
>

```idris
reg_exp_ex2 : [1,2] =~ (App (Chr 1) (Chr 2))
reg_exp_ex2 = MApp {s1=[1]} {s2=[2]} MChar MChar
```

Notice how the last example applies \idr{MApp} to the strings \idr{[1]} and
\idr{[2]} directly. While the goal mentions \idr{[1,2]} instead of \idr{[1] ++
[2]}, Idris is able to figure out how to split the string on its own, so we can
drop the implicits:

> reg_exp_ex2 : [1,2] =~ (App (Chr 1) (Chr 2))
> reg_exp_ex2 = MApp MChar MChar
>

Using pattern matching, we can also show that certain strings do not match a
regular expression:

> reg_exp_ex3 : Not ([1,2] =~ (Chr 1))
> reg_exp_ex3 MEmpty impossible
> reg_exp_ex3 MChar impossible
> reg_exp_ex3 (MApp _ _) impossible
> reg_exp_ex3 (MUnionL _) impossible
> reg_exp_ex3 (MUnionR _) impossible
> reg_exp_ex3 MStar0 impossible
> reg_exp_ex3 (MStarApp _ _) impossible
>

We can define helper functions to help write down regular expressions. The
\idr{reg_exp_of_list} function constructs a regular expression that matches
exactly the list that it receives as an argument:

> reg_exp_of_list : List t -> Reg_exp t
> reg_exp_of_list [] = EmptyStr
> reg_exp_of_list (x :: xs) = App (Chr x) (reg_exp_of_list xs)
>
> reg_exp_ex4 : [1,2,3] =~ (reg_exp_of_list [1,2,3])
> reg_exp_ex4 = MApp MChar $ MApp MChar $ MApp MChar MEmpty
>

We can also prove general facts about \idr{Exp_match}. For instance, the
following lemma shows that every string \idr{s} that matches \idr{re} also
matches \idr{Star re}.

> MStar1 : (s =~ re) -> (s =~ Star re)
> MStar1 {s} h =
>   rewrite sym $ appendNilRightNeutral s in
>   MStarApp h MStar0
>

(Note the use of \idr{appendNilRightNeutral} to change the goal of the theorem
to exactly the same shape expected by \idr{MStarApp}.)


==== Exercise: 3 stars (exp_match_ex1)

The following lemmas show that the informal matching rules given at the
beginning of the chapter can be obtained from the formal inductive definition.

> empty_is_empty : Not (s =~ EmptySet)
> empty_is_empty = ?empty_is_empty_rhs
>
> MUnion' : (s =~ re1, s =~ re2) -> s =~ Union re1 re2
> MUnion' m = ?MUnion'_rhs
>

The next lemma is stated in terms of the \idr{fold} function from the \idr{Poly}
chapter: If \idr{ss : List (List t)} represents a sequence of strings \idr{s1,
..., sn}, then \idr{fold (++) ss []} is the result of concatenating them all
together.

\todo[inline]{Copied these here for now, add hyperlink}

> fold : (f : x -> y -> y) -> (l : List x) -> (b : y) -> y
> fold f [] b = b
> fold f (h::t) b = f h (fold f t b)
>
> In : (x : a) -> (l : List a) -> Type
> In x [] = Void
> In x (x' :: xs) = (x' = x) `Either` In x xs
>
> MStar' : ((s : List t) -> (In s ss) -> (s =~ re)) ->
>          (fold (++) ss []) =~ Star re
> MStar' f = ?MStar'_rhs
>

$\square$


==== Exercise: 4 stars (reg_exp_of_list)

Prove that \idr{reg_exp_of_list} satisfies the following specification:

> reg_exp_of_list_spec : (s1 =~ reg_exp_of_list s2) <-> (s1 = s2)
> reg_exp_of_list_spec = ?reg_exp_of_list_spec_rhs
>

$\square$

Since the definition of \idr{Exp_match} has a recursive structure, we might
expect that proofs involving regular expressions will often require induction on
evidence. For example, suppose that we wanted to prove the following intuitive
result: If a regular expression \idr{re} matches some string \idr{s}, then all
elements of \idr{s} must occur somewhere in \idr{re}. To state this theorem, we
first define a function \idr{re_chars} that lists all characters that occur in a
regular expression:

> re_chars : (re : Reg_exp t) -> List t
> re_chars EmptySet        = []
> re_chars EmptyStr        = []
> re_chars (Chr x)         = [x]
> re_chars (App re1 re2)   = re_chars re1 ++ re_chars re2
> re_chars (Union re1 re2) = re_chars re1 ++ re_chars re2
> re_chars (Star re)       = re_chars re
>
> re_star : re_chars (Star re) = re_chars re
> re_star = Refl
>

We can then phrase our theorem as follows:

\todo[inline]{Copied here for now}

> in_app_iff : (In a (l++l')) <-> (In a l `Either` In a l')
> in_app_iff {l} {l'} = (to l l', fro l l')
> where
>   to : (l, l' : List x) -> In a (l ++ l') -> (In a l) `Either` (In a l')
>   to [] [] prf = absurd prf
>   to [] _ prf = Right prf
>   to (_ :: _) _ (Left Refl) = Left $ Left Refl
>   to (_ :: xs) l' (Right prf) =
>     case to xs l' prf of
>       Left ixs => Left $ Right ixs
>       Right il' => Right il'
>   fro : (l, l' : List x) -> (In a l) `Either` (In a l') -> In a (l ++ l')
>   fro [] _ (Left prf) = absurd prf
>   fro (_ :: _) _ (Left (Left Refl)) = Left Refl
>   fro (_ :: xs) l' (Left (Right prf)) = Right $ fro xs l' (Left prf)
>   fro _ [] (Right prf) = absurd prf
>   fro [] _ (Right prf) = prf
>   fro (_ :: ys) l' prf@(Right _) = Right $ fro ys l' prf

\todo[inline]{Some unfortunate implicit plumbing}

> destruct : In x (s1 ++ s2) -> (In x s1) `Either` (In x s2)
> destruct {x} {s1} {s2} = fst $ in_app_iff {a=x} {l=s1} {l'=s2}
>
> construct : (In x (re_chars re1)) `Either` (In x (re_chars re2)) ->
>             In x ((re_chars re1) ++ (re_chars re2))
> construct {x} {re1} {re2} =
>   snd $ in_app_iff {a=x} {l=(re_chars re1)} {l'=(re_chars re2)}
>
> in_re_match : (s =~ re) -> In x s -> In x (re_chars re)
> in_re_match MEmpty prf = prf
> in_re_match MChar prf = prf
> in_re_match (MApp m1 m2) prf = construct $ case destruct prf of
>     Left prf1 => Left $ in_re_match m1 prf1
>     Right prf2 => Right $ in_re_match m2 prf2
> in_re_match (MUnionL ml) prf = construct $ Left $ in_re_match ml prf
> in_re_match (MUnionR mr) prf = construct $ Right $ in_re_match mr prf
> in_re_match MStar0 prf = absurd prf
> in_re_match (MStarApp m ms) prf = case destruct prf of

\todo[inline]{Edit}

Something interesting happens in the \idr{MStarApp} case. We obtain two
induction hypotheses: One that applies when \idr{x} occurs in \idr{s1} (which
matches \idr{re}), and a second one that applies when \idr{x} occurs in \idr{s2}
(which matches \idr{Star re}). This is a good illustration of why we need
induction on evidence for \idr{Exp_match}, as opposed to \idr{re}: The latter
would only provide an induction hypothesis for strings that match \idr{re},
which would not allow us to reason about the case \idr{In x s2}.

>     Left prf' => in_re_match m prf'
>     Right prfs => in_re_match ms prfs
>


==== Exercise: 4 stars (re_not_empty)

Write a recursive function \idr{re_not_empty} that tests whether a regular
expression matches some string. Prove that your function is correct.

> re_not_empty : (re : Reg_exp t) -> Bool
> re_not_empty re = ?re_not_empty_rhs
>
> re_not_empty_correct : (s ** s =~ re) <-> re_not_empty re = True
> re_not_empty_correct = ?re_not_empty_correct_rhs
>

$\square$


=== The remember Tactic

\ \todo[inline]{Rewrite the section, dependent pattern matching figures all of
this out}

One potentially confusing feature of the induction tactic is that it happily
lets you try to set up an induction over a term that isn't sufficiently general.
The effect of this is to lose information (much as destruct can do), and leave
you unable to complete the proof. Here's an example:

> star_app : (s1 =~ Star re) -> (s2 =~ Star re) -> (s1 ++ s2) =~ Star re
> star_app MStar0 m2 = m2
> star_app {s2} (MStarApp {s1=s11} {s2=s21} m ms) m2 =
>  rewrite sym $ appendAssociative s11 s21 s2 in
>    MStarApp m (star_app ms m2)
>

Just doing an inversion on H1 won't get us very far in the recursive cases. (Try
it!). So we need induction. Here is a naive first attempt:

```coq
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
```

But now, although we get seven cases (as we would expect from the definition of
Exp_match), we have lost a very important bit of information from H1: the fact
that s1 matched something of the form Star re. This means that we have to give
proofs for all seven constructors of this definition, even though all but two of
them (MStar0 and MStarApp) are contradictory. We can still get the proof to go
through for a few constructors, such as MEmpty...

```coq
  - (* MEmpty *)
    simpl. intros H. apply H.
```

... but most cases get stuck. For MChar, for instance, we must show that

```coq
    s2 =~ Char x' -> x' :: s2 =~ Char x',
```

which is clearly impossible.

```coq
  - (* MChar. Stuck... *)
Abort.
```

The problem is that induction over a Type hypothesis only works properly with
hypotheses that are completely general, i.e., ones in which all the arguments
are variables, as opposed to more complex expressions, such as Star re.

(In this respect, induction on evidence behaves more like destruct than like
inversion.)

We can solve this problem by generalizing over the problematic expressions with
an explicit equality:

```coq
Lemma star_app: forall T (s1 s2 : list T) (re re' : Reg_exp T),
  s1 =~ re' ->
  re' = Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
```

We can now proceed by performing induction over evidence directly, because the
argument to the first hypothesis is sufficiently general, which means that we
can discharge most cases by inverting the re' = Star re equality in the context.

This idiom is so common that Idris provides a tactic to automatically generate
such equations for us, avoiding thus the need for changing the statements of our
theorems.

Invoking the tactic remember e as x causes Idris to (1) replace all occurrences
of the expression e by the variable x, and (2) add an equation x = e to the
context. Here's how we can use it to show the above result:

```coq
Abort.

Lemma star_app: forall T (s1 s2 : list T) (re : Reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
```

We now have Heqre' : re' = Star re.

```coq
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
```

The Heqre' is contradictory in most cases, which allows us to conclude
immediately.

```coq
  - (* MEmpty *) inversion Heqre'.
  - (* MChar *) inversion Heqre'.
  - (* MApp *) inversion Heqre'.
  - (* MUnionL *) inversion Heqre'.
  - (* MUnionR *) inversion Heqre'.
```

The interesting cases are those that correspond to Star. Note that the induction
hypothesis IH2 on the MStarApp case mentions an additional premise Star re'' =
Star re', which results from the equality generated by remember.

```coq
  - (* MStar0 *)
    inversion Heqre'. intros s H. apply H.

  - (* MStarApp *)
    inversion Heqre'. rewrite H0 in IH2, Hmatch1.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * reflexivity.
      * apply H1.
Qed.
```


==== Exercise: 4 stars (exp_match_ex2)

The \idr{MStar''} lemma below (combined with its converse, the \idr{MStar'}
exercise above), shows that our definition of \idr{Exp_match} for \idr{Star} is
equivalent to the informal one given previously.

> MStar'' : (s =~ Star re) ->
>           (ss : List (List t) **
>                (s = fold (++) ss [], (s': List t) -> In s' ss -> s' =~ re)
>           )
> MStar'' m = ?MStar''_rhs
>

$\square$


==== Exercise: 5 stars, advanced (pumping)

One of the first really interesting theorems in the theory of regular
expressions is the so-called _pumping lemma_, which states, informally, that any
sufficiently long string \idr{s} matching a regular expression \idr{re} can be
"pumped" by repeating some middle section of \idr{s} an arbitrary number of
times to produce a new string also matching \idr{re}.

To begin, we need to define "sufficiently long." Since we are working in a
constructive logic, we actually need to be able to calculate, for each regular
expression \idr{re}, the minimum length for strings \idr{s} to guarantee
"pumpability."

> namespace Pumping
>
>   pumping_constant : (re : Reg_exp t) -> Nat
>   pumping_constant EmptySet        = 0
>   pumping_constant EmptyStr        = 1
>   pumping_constant (Chr _)         = 2
>   pumping_constant (App re1 re2)   =
>     pumping_constant re1 + pumping_constant re2
>   pumping_constant (Union re1 re2) =
>     pumping_constant re1 + pumping_constant re2
>   pumping_constant (Star _)        = 1
>

Next, it is useful to define an auxiliary function that repeats a string
(appends it to itself) some number of times.

>   napp : (n : Nat) -> (l : List t) -> List t
>   napp Z _     = []
>   napp (S k) l = l ++ napp k l
>
>   napp_plus: (n, m : Nat) -> (l : List t) ->
>              napp (n + m) l = napp n l ++ napp m l
>   napp_plus Z _ _     = Refl
>   napp_plus (S k) m l =
>    rewrite napp_plus k m l in
>      appendAssociative l (napp k l) (napp m l)
>

Now, the pumping lemma itself says that, if \idr{s =~ re} and if the length of
\idr{s} is at least the pumping constant of \idr{re}, then \idr{s} can be split
into three substrings \idr{s1 ++ s2 ++ s3} in such a way that \idr{s2} can be
repeated any number of times and the result, when combined with \idr{s1} and
\idr{s3} will still match \idr{re}. Since \idr{s2} is also guaranteed not to be
the empty string, this gives us a (constructive!) way to generate strings
matching \idr{re} that are as long as we like.

>   pumping : (s =~ re) -> ((pumping_constant re) <=' (length s))
>             -> (s1 ** s2 ** s3 ** ( s = s1 ++ s2 ++ s3
>                                   , Not (s2 = [])
>                                   , (m:Nat) -> (s1 ++ napp m s2 ++ s3) =~ re
>                                   ))

\todo[inline]{Edit hint}

To streamline the proof (which you are to fill in), the `omega` tactic, which is
enabled by the following `Require`, is helpful in several places for
automatically completing tedious low-level arguments involving equalities or
inequalities over natural numbers. We'll return to `omega` in a later chapter,
but feel free to experiment with it now if you like. The first case of the
induction gives an example of how it is used.

>   pumping m le = ?pumping_rhs
>


== Case Study: Improving Reflection

We've seen in the \idr{Logic} chapter that we often need to relate boolean
computations to statements in \idr{Type}. But performing this conversion in the
way we did it there can result in tedious proof scripts. Consider the proof of
the following theorem:

\todo[inline]{Copy here for now}

> beq_nat_true : beq_nat n m = True -> n = m
> beq_nat_true {n=Z} {m=Z} _ = Refl
> beq_nat_true {n=(S _)} {m=Z} Refl impossible
> beq_nat_true {n=Z} {m=(S _)} Refl impossible
> beq_nat_true {n=(S n')} {m=(S m')} eq =
>  rewrite beq_nat_true {n=n'} {m=m'} eq in Refl
>
> filter_not_empty_In : Not (filter (beq_nat n) l = []) -> In n l
> filter_not_empty_In {l=[]} contra = contra Refl
> filter_not_empty_In {l=(x::_)} {n} contra with (beq_nat n x) proof h
>   filter_not_empty_In contra | True =
>     Left $ sym $ beq_nat_true $ sym h
>   filter_not_empty_In contra | False =
>     Right $ filter_not_empty_In contra
>

In the second case we explicitly apply the \idr{beq_nat_true} lemma to the
equation generated by doing a dependent match on \idr{beq_nat n x}, to convert
the assumption \idr{beq_nat n x = True} into the assumption \idr{n = m}.

We can streamline this by defining an inductive proposition that yields a better
case-analysis principle for \idr{beq_nat n m}. Instead of generating an equation
such as \idr{beq_nat n m = True}, which is generally not directly useful, this
principle gives us right away the assumption we really need: \idr{n = m}.

We'll actually define something a bit more general, which can be used with
arbitrary properties (and not just equalities):

```idris
data Reflect : Type -> Bool -> Type where
  ReflectT : (p : Type) -> Reflect p True
  ReflectF : (p : Type) -> (Not p) -> Reflect p False
```

\todo[inline]{Seems that additional `(b=True/False)` constructor parameter is
needed for this to work in Idris. Update the text.`}

Before explaining this, let's rearrange it a little: Since the types of both
\idr{ReflectT} and \idr{ReflectF} begin with \idr{(p : Type)}, we can make the
definition a bit more readable and easier to work with by making \idr{p} a
parameter of the whole \idr{data} declaration.

> data Reflect : (p : Type) -> (b : Bool) -> Type where
>   ReflectT : p -> (b=True) -> Reflect p b
>   ReflectF : (Not p) -> (b=False) -> Reflect p b
>

The reflect property takes two arguments: a proposition \idr{p} and a boolean
\idr{b}. Intuitively, it states that the property \idr{p} is _reflected_ in
(i.e., equivalent to) the boolean \idr{b}: \idr{p} holds if and only if \idr{b =
True}. To see this, notice that, by definition, the only way we can produce
evidence that \idr{Reflect p True} holds is by showing that \idr{p} is true and
using the \idr{ReflectT} constructor. If we invert this statement, this means
that it should be possible to extract evidence for \idr{p} from a proof of
\idr{Reflect p True}. Conversely, the only way to show \idr{Reflect p False} is
by combining evidence for \idr{Not p} with the \idr{ReflectF} constructor.

It is easy to formalize this intuition and show that the two statements are
indeed equivalent:

> iff_reflect : (p <-> (b = True)) -> Reflect p b
> iff_reflect {b = False} (pb, _) = ReflectF (uninhabited . pb) Refl
> iff_reflect {b = True} (_, bp) = ReflectT (bp Refl) Refl
>


==== Exercise: 2 stars, recommended (reflect_iff)

> reflect_iff : Reflect p b -> (p <-> (b = True))
> reflect_iff x = ?reflect_iff_rhs
>

$\square$

The advantage of \idr{Reflect} over the normal "if and only if" connective is
that, by destructing a hypothesis or lemma of the form \idr{Reflect p b}, we can
perform case analysis on \idr{b} while at the same time generating appropriate
hypothesis in the two branches (\idr{p} in the first subgoal and \idr{Not p} in
the second).

\todo[inline]{Copy here for now}

> beq_nat_true_iff : (n1, n2 : Nat) -> (beq_nat n1 n2 = True) <-> (n1 = n2)
> beq_nat_true_iff n1 n2 = (to, fro n1 n2)
> where
>   to : (beq_nat n1 n2 = True) -> (n1 = n2)
>   to = beq_nat_true {n=n1} {m=n2}
>   fro : (n1, n2 : Nat) -> (n1 = n2) -> (beq_nat n1 n2 = True)
>   fro n1 n1 Refl = sym $ beq_nat_refl n1

>
> iff_sym : (p <-> q) -> (q <-> p)
> iff_sym (pq, qp) = (qp, pq)
>
> beq_natP : Reflect (n = m) (beq_nat n m)
> beq_natP {n} {m} = iff_reflect $ iff_sym $ beq_nat_true_iff n m
>

\todo[inline]{Edit - we basically trade the invocation of \idr{beq_nat_true} in
\idr{Left} for an indirect rewrite in \idr{Right}}

The new proof of \idr{filter_not_empty_In} now goes as follows. Notice how the
calls to destruct and apply are combined into a single call to destruct.

(To see this clearly, look at the two proofs of \idr{filter_not_empty_In} with
Idris and observe the differences in proof state at the beginning of the first
case of the destruct.)

> filter_not_empty_In' : Not (filter (beq_nat n) l = []) -> In n l
> filter_not_empty_In' {l=[]} contra = contra Refl
> filter_not_empty_In' {n} {l=(x::xs)} contra with (beq_natP {n} {m=x})
>   filter_not_empty_In' _ | (ReflectT eq _) = Left $ sym eq
>   filter_not_empty_In' {n} {l=(x::xs)} contra | (ReflectF _ notbeq) = let

\todo[inline]{How to rewrite more neatly here?}

>     contra' = replace notbeq contra {P = \a => Not ((if a
>                                       then x :: filter (beq_nat n) xs
>                                       else filter (beq_nat n) xs) = [])}
>   in Right $ filter_not_empty_In' contra'
>


==== Exercise: 3 stars, recommended (beq_natP_practice)

Use \idr{beq_natP} as above to prove the following:

> count : (n : Nat) -> (l : List Nat) -> Nat
> count _ [] = 0
> count n (x :: xs) = (if beq_nat n x then 1 else 0) + count n xs
>
> beq_natP_practice : count n l = 0 -> Not (In n l)
> beq_natP_practice prf = ?beq_natP_practice_rhs
>

$\square$

This technique gives us only a small gain in convenience for the proofs we've
seen here, but using \idr{Reflect} consistently often leads to noticeably shorter and
clearer scripts as proofs get larger. We'll see many more examples in later
chapters.

\todo[inline]{Add http://math-comp.github.io/math-comp/ as a link}

The use of the reflect property was popularized by `SSReflect`, a Coq library
that has been used to formalize important results in mathematics, including as
the 4-color theorem and the Feit-Thompson theorem. The name `SSReflect` stands
for _small-scale reflection_, i.e., the pervasive use of reflection to simplify
small proof steps with boolean computations.


== Additional Exercises


==== Exercise: 3 stars, recommended (nostutter)

Formulating inductive definitions of properties is an important skill you'll
need in this course. Try to solve this exercise without any help at all.

We say that a list "stutters" if it repeats the same element consecutively. The
property "\idr{Nostutter mylist}" means that \idr{mylist} does not stutter.
Formulate an inductive definition for \idr{Nostutter}. (This is different from
the \idr{NoDup} property in the exercise below; the sequence \idr{[1,4,1]}
repeats but does not stutter.)

> data Nostutter : List t -> Type where
>   -- FILL IN HERE
>   RemoveMe : Nostutter [] -- needed for typechecking, data shouldn't be empty
>

Make sure each of these tests succeeds, but feel free to change the suggested
proof (in comments) if the given one doesn't work for you. Your definition might
be different from ours and still be correct, in which case the examples might
need a different proof. (You'll notice that the suggested proofs use a number of
tactics we haven't talked about, to make them more robust to different possible
ways of defining \idr{Nostutter}. You can probably just uncomment and use them
as-is, but you can also prove each example with more basic tactics.)

> test_nostutter_1 : Nostutter [3,1,4,1,5,6]
> test_nostutter_1 = ?test_nostutter_1_rhs
>

```coq
(*
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
*)
```

> test_nostutter_2 : Nostutter []
> test_nostutter_2 = ?test_nostutter_2_rhs
>

```coq
(*
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
*)
```

> test_nostutter_3 : Nostutter [5]
> test_nostutter_3 = ?test_nostutter_3_rhs
>

```coq
(*
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)
```

> test_nostutter_4 : Not (Nostutter [3,1,1,4])
> test_nostutter_4 = ?test_nostutter_4_rhs
>

```coq
(*
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H1; auto. Qed.
*)
```

$\square$


==== Exercise: 4 stars, advanced (filter_challenge)

Let's prove that our definition of \idr{filter} from the \idr{Poly} chapter
matches an abstract specification. Here is the specification, written out
informally in English:

A list \idr{l} is an "in-order merge" of \idr{l1} and \idr{l2} if it contains
all the same elements as \idr{l1} and \idr{l2}, in the same order as \idr{l1}
and \idr{l2}, but possibly interleaved. For example,

```idris
    [1,4,6,2,3]
```

is an in-order merge of

```idris
    [1,6,2]
```

and

```idris
    [4,3]
```

Now, suppose we have a set \idr{t}, a function \idr{test : t->Bool}, and a list
\idr{l} of type \idr{List t}. Suppose further that \idr{l} is an in-order merge
of two lists, \idr{l1} and \idr{l2}, such that every item in \idr{l1} satisfies
\idr{test} and no item in \idr{l2} satisfies \idr{test}. Then \idr{filter test l
= l1}.

Translate this specification into a Idris theorem and prove it. (You'll need to
begin by defining what it means for one list to be a merge of two others. Do
this with an inductive \idr{data} type, not a function.)

> -- FILL IN HERE
>

$\square$


==== Exercise: 5 stars, advanced, optional (filter_challenge_2)

A different way to characterize the behavior of \idr{filter} goes like this:
Among all subsequences of \idr{l} with the property that \idr{test} evaluates to
\idr{True} on all their members, \idr{filter test l} is the longest. Formalize
this claim and prove it.

> -- FILL IN HERE
>

$\square$


==== Exercise: 4 stars, optional (palindromes)

A palindrome is a sequence that reads the same backwards as forwards.

  - Define an inductive proposition \idr{Pal} on \idr{List t} that captures what
    it means to be a palindrome. (Hint: You'll need three cases. Your definition
    should be based on the structure of the list; just having a single
    constructor like

```idris
    C : (l : List t) -> l = rev l -> Pal l
```

    may seem obvious, but will not work very well.)

  - Prove (\idr{pal_app_rev}) that

```idris
    (l : List t) -> Pal (l ++ rev l)
```

  - Prove (\idr{pal_rev}) that

```idris
    (l : List t) -> Pal l -> l = rev l
```

> -- FILL IN HERE
>

$\square$


==== Exercise: 5 stars, optional (palindrome_converse)

Again, the converse direction is significantly more difficult, due to the lack
of evidence. Using your definition of \idr{Pal} from the previous exercise,
prove that

```idris
    (l : List t) -> l = rev l -> Pal l
```

> -- FILL IN HERE
>

$\square$


=== Exercise: 4 stars, advanced, optional (NoDup)

Recall the definition of the \idr{In} property from the \idr{Logic} chapter, which asserts
that a value \idr{x} appears at least once in a list \idr{l}:

```idris
In : (x : t) -> (l : List t) -> Type
In x [] = Void
In x (x' :: xs) = (x' = x) `Either` In x xs
```

Your first task is to use \idr{In} to define a proposition \idr{Disjoint {t} l1
l2}, which should be provable exactly when \idr{l1} and \idr{l2} are lists (with
elements of type \idr{t}) that have no elements in common.

> -- FILL IN HERE
>

Next, use \idr{In} to define an inductive proposition \idr{NoDup {t} l}, which
should be provable exactly when \idr{l} is a list (with elements of type
\idr{t}) where every member is different from every other. For example,
\idr{NoDup {t=Nat} [1,2,3,4]} and \idr{NoDup {t=Bool} []} should be provable,
while \idr{NoDup {t=Nat} [1,2,1]} and \idr{NoDup {t=Bool} [True,True]} should
not be.

> -- FILL IN HERE
>

Finally, state and prove one or more interesting theorems relating
\idr{Disjoint}, \idr{NoDup} and \idr{(++)} (list append).

> -- FILL IN HERE
>

$\square$


==== Exercise: 4 stars, advanced, optional (pigeonhole principle)

The _pigeonhole principle_ states a basic fact about counting: if we distribute
more than \idr{n} items into \idr{n} pigeonholes, some pigeonhole must contain
at least two items. As often happens, this apparently trivial fact about numbers
requires non-trivial machinery to prove, but we now have enough...

First prove an easy useful lemma.

> in_split : In x l -> (l1 ** l2 ** l = l1 ++ x :: l2)
> in_split prf = ?in_split_rhs
>

Now define a property \idr{Repeats} such that \idr{Repeats {t} l} asserts that
\idr{l} contains at least one repeated element (of type \idr{t}).

> data Repeats : List t -> Type where
>   -- FILL IN HERE
>   RemoveMe' : Repeats [] -- needed for typechecking, data shouldn't be empty
>

Now, here's a way to formalize the pigeonhole principle. Suppose list \idr{l2}
represents a list of pigeonhole labels, and list \idr{l1} represents the labels
assigned to a list of items. If there are more items than labels, at least two
items must have the same label -- i.e., list \idr{l1} must contain repeats.

This proof is much easier if you use the \idr{excluded_middle} hypothesis to
show that \idr{In} is decidable, i.e., \idr{(In x l) `Either` (Not (In x l))}.
However, it is also possible to make the proof go through _without_ assuming
that \idr{In} is decidable; if you manage to do this, you will not need the
\idr{excluded_middle} hypothesis.

> pigeonhole_principle : ((x : t) -> In x l1 -> In x l2) ->
>                        ((length l2) <' (length l1)) ->
>                        Repeats l1
> pigeonhole_principle f prf = ?pigeonhole_principle_rhs
>   where
>     excluded_middle : (p : Type) -> p `Either` (Not p)
>     excluded_middle p = really_believe_me p
>

$\square$
