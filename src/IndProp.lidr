= IndProp : Inductively Defined Propositions

> module IndProp

> import Induction

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

This definition is different in one crucial respect from previous uses of
\idr{data}: its result is not a \idr{Type}, but rather a function from \idr{Nat}
to \idr{Type} -- that is, a property of numbers. Note that we've already seen
other inductive definitions that result in functions, such as \idr{List}, whose
type is \idr{Type -> Type}. What is new here is that, because the \idr{Nat}
argument of \idr{Ev} appears unnamed, to the right of the colon, it is allowed
to take different values in the types of different constructors: \idr{Z} in the
type of \idr{Ev_0} and \idr{S (S n)} in the type of \idr{Ev_SS}.

In contrast, the definition of \idr{List} names the \idr{x} parameter globally, forcing the result of \idr{Nil} and \idr{(::)} to be the same (\idr{List x}). Had we
tried to name \idr{Nat} in defining \idr{Ev}, we would have seen an error:

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

\todo[inline]{Edit explanation}

("Parameter" here is Idris jargon for an argument on the left of the colon in an
Inductive definition; "index" is used to refer to arguments on the right of the
colon.)

We can think of the definition of \idr{Ev} as defining a Idris property \idr{Ev
: Nat -> Type}, together with theorems \idr{Ev_0 : Ev Z} and \idr{Ev_SS : n ->
Ev n -> Ev (S (S n))}. Such "constructor theorems" have the same status as
proven theorems. In particular, we can apply rule names as functions to each
other to prove \idr{Ev} for particular numbers...

> ev_4 : Ev 4
> ev_4 = Ev_SS {n=2} $ Ev_SS {n=0} Ev_0

We can also prove theorems that have hypotheses involving \idr{Ev}.

> ev_plus4 : Ev n -> Ev (4 + n)
> ev_plus4 x = Ev_SS $ Ev_SS x

More generally, we can show that any number multiplied by 2 is even:


==== Exercise: 1 star (ev_double)

> ev_double : Ev (double n)
> ev_double = ?ev_double_rhs

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

\todo[inline]{Edit}

Suppose we are proving some fact involving a number \idr{n}, and we are given \idr{Ev n} as
a hypothesis. We already know how to perform case analysis on \idr{n} using the
\idr{inversion} tactic, generating separate subgoals for the case where \idr{n = Z} and the
case where \idr{n = S n'} for some \idr{n'}. But for some proofs we may instead want to
analyze the evidence that \idr{Ev n} directly.

By the definition of \idr{Ev}, there are two cases to consider:

  - If the evidence is of the form \idr{Ev_0}, we know that \idr{n = Z}.
  
  - Otherwise, the evidence must have the form \idr{Ev_SS {n=n'} e'}, where
    \idr{n = S (S n')} and \idr{e'} is evidence for \idr{Ev n'}.

\todo[inline]{Edit}

We can perform this kind of reasoning in Idris, again using pattern matching.
Besides allowing us to reason about equalities involving constructors,
\idr{inversion} provides a case-analysis principle for inductively defined
propositions. When used in this way, its syntax is similar to \idr{destruct}: We
pass it a list of identifiers separated by \idr{|} characters to name the
arguments to each of the possible constructors.

> ev_minus2 : Ev n -> Ev (pred (pred n))
> ev_minus2 Ev_0 = Ev_0
> ev_minus2 (Ev_SS e') = e'

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

\todo[inline]{Edit to say that dependent pattern match is smart enough}

Intuitively, we know that evidence for the hypothesis cannot consist just of the
\idr{Ev_0} constructor, since O and S are different constructors of the type
Nat; hence, \idr{Ev_SS} is the only case that applies. Unfortunately, destruct
is not smart enough to realize this, and it still generates two subgoals. Even
worse, in doing so, it keeps the final goal unchanged, failing to provide any
useful information for completing the proof.

The inversion tactic, on the other hand, can detect (1) that the first case does
not apply, and (2) that the n' that appears on the \idr{Ev_SS} case must be the
same as n. This allows us to complete the proof

> evSS_ev (Ev_SS e') = e'

By using dependent pattern matching, we can also apply the principle of
explosion to "obviously contradictory" hypotheses involving inductive
properties. For example:

> one_not_even : Not (Ev 1)
> one_not_even Ev_0 impossible
> one_not_even (Ev_SS _) impossible


=== Exercise: 1 star (inversion_practice)

Prove the following results using pattern matching.

> SSSSev__even : Ev (S (S (S (S n)))) -> Ev n
> SSSSev__even e = ?SSSSev__even_rhs

> even5_nonsense : Ev 5 -> 2 + 2 = 9
> even5_nonsense e = ?even5_nonsense_rhs

$\square$

\todo[inline]{Edit}

The way we've used inversion here may seem a bit mysterious at first. Until now,
we've only used inversion on equality propositions, to utilize injectivity of
constructors or to discriminate between different constructors. But we see here
that inversion can also be applied to analyzing evidence for inductively defined
propositions.

Here's how inversion works in general. Suppose the name I refers to an
assumption P in the current context, where P has been defined by an Inductive
declaration. Then, for each of the constructors of P, inversion I generates a
subgoal in which I has been replaced by the exact, specific conditions under
which this constructor could have been used to prove P. Some of these subgoals
will be self-contradictory; inversion throws these away. The ones that are left
represent the cases that must be proved to establish the original goal. For
those, inversion adds all equations into the proof context that must hold of the
arguments given to P (e.g., S (S n') = n in the proof of \idr{evSS_ev}).

The \idr{ev_double} exercise above shows that our new notion of evenness is
implied by the two earlier ones (since, by \idr{even_bool_prop} in chapter
`Logic`, we already know that those are equivalent to each other). To show that
all three coincide, we just need the following lemma:

> ev_even_firsttry : Ev n -> (k ** n = double k)

We proceed by case analysis on \idr{Ev n}. The first case can be solved
trivially.

> ev_even_firsttry Ev_0 = (Z ** Refl)

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

> ev_even_firsttry (Ev_SS e') = I $ ev_even_firsttry e'
> where
>   I : (k' ** n' = double k') -> (k ** S (S n') = double k)
>   I (k' ** prf) = (S k' ** cong {f=S} $ cong {f=S} prf)


=== Induction on Evidence

\todo[inline]{Edit}

If this looks familiar, it is no coincidence: We've encountered similar problems
in the `Induction` chapter, when trying to use case analysis to prove results
that required induction. And once again the solution is... induction!

The behavior of induction on evidence is the same as its behavior on data: It
causes Idris to generate one subgoal for each constructor that could have used
to build that evidence, while providing an induction hypotheses for each
recursive occurrence of the property in question.

Let's try our current lemma again:

Lemma ev_even : ∀n,
  ev n -> (k **  n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    ∃0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. ∃(S k'). reflexivity.
Qed.

Here, we can see that Idris produced an IH that corresponds to E', the single recursive occurrence of ev in its own definition. Since E' mentions n', the induction hypothesis talks about n', as opposed to n or some other number.
The equivalence between the second and third definitions of evenness now follows.

Theorem ev_even_iff : ∀n,
  ev n ↔ (k **  n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

As we will see in later chapters, induction on evidence is a recurring technique across many areas, and in particular when formalizing the semantics of programming languages, where many properties of interest are defined inductively.
The following exercises provide simple examples of this technique, to help you familiarize yourself with it.
Exercise: 2 stars (ev_sum)
Theorem ev_sum : ∀n m, ev n -> ev m -> ev (n + m).
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
Exercise: 4 stars, advanced, optional (ev_alternate)
In general, there may be multiple ways of defining a property inductively. For example, here's a (slightly contrived) alternative definition for ev:

Inductive ev' : Nat -> Type =
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : ∀n m, ev' n -> ev' m -> ev' (n + m).

Prove that this definition is logically equivalent to the old one. (You may want to look at the previous theorem when you get to the induction step.)

Theorem ev'_ev : ∀n, ev' n ↔ ev n.
Proof.
 (* FILL IN HERE *) Admitted.
$\square$
Exercise: 3 stars, advanced, recommended (ev_ev__ev)
Finding the appropriate thing to do induction on is a bit tricky here:

Theorem ev_ev__ev : ∀n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
Exercise: 3 stars, optional (ev_plus_plus)
This exercise just requires applying existing lemmas. No induction or even case analysis is needed, though some of the rewriting may be tedious.

Theorem ev_plus_plus : ∀n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* FILL IN HERE *) Admitted.
$\square$

Inductive Relations
A proposition parameterized by a number (such as ev) can be thought of as a property -- i.e., it defines a subset of Nat, namely those numbers for which the proposition is provable. In the same way, a two-argument proposition can be thought of as a relation -- i.e., it defines a set of pairs for which the proposition is provable.

Module Playground.

One useful example is the "less than or equal to" relation on numbers.
The following definition should be fairly intuitive. It says that there are two ways to give evidence that one number is less than or equal to another: either observe that they are the same number, or give evidence that the first is less than or equal to the predecessor of the second.

Inductive le : Nat -> Nat -> Type =
  | le_n : ∀n, le n n
  | le_S : ∀n m, (le n m) -> (le n (S m)).

Notation "m <= n" = (le m n).

Proofs of facts about <= using the constructors le_n and le_S follow the same patterns as proofs about properties, like ev above. We can apply the constructors to prove <= goals (e.g., to show that 3<=3 or 3<=6), and we can use tactics like inversion to extract information from <= hypotheses in the context (e.g., to prove that (2 <= 1) -> 2+2=5.)
Here are some sanity checks on the definition. (Notice that, although these are the same kind of simple "unit tests" as we gave for the testing functions we wrote in the first few lectures, we must construct their proofs explicitly -- simpl and reflexivity don't do the job, because the proofs aren't just a matter of simplifying computations.)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n. Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2. Qed.

The "strictly less than" relation n < m can now be defined in terms of le.

End Playground.

Definition lt (n m:Nat) = le (S n) m.

Notation "m < n" = (lt m n).

Here are a few more simple relations on numbers:

Inductive square_of : Nat -> Nat -> Type =
  | sq : ∀n:Nat, square_of n (n * n).

Inductive next_nat : Nat -> Nat -> Type =
  | nn : ∀n:Nat, next_nat n (S n).

Inductive next_even : Nat -> Nat -> Type =
  | ne_1 : ∀n, ev (S n) -> next_even n (S n)
  | ne_2 : ∀n, ev (S (S n)) -> next_even n (S (S n)).

Exercise: 2 stars, optional (total_relation)
Define an inductive binary relation total_relation that holds between every pair of natural numbers.

(* FILL IN HERE *)
$\square$
Exercise: 2 stars, optional (empty_relation)
Define an inductive binary relation empty_relation (on numbers) that never holds.

(* FILL IN HERE *)
$\square$
Exercise: 3 stars, optional (le_exercises)
Here are a number of facts about the <= and < relations that we are going to need later in the course. The proofs make good practice exercises.

Lemma le_trans : ∀m n o, m <= n -> n <= o -> m <= o.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem O_le_n : ∀n,
  0 <= n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem n_le_m__Sn_le_Sm : ∀n m,
  n <= m -> S n <= S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem Sn_le_Sm__n_le_m : ∀n m,
  S n <= S m -> n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem le_plus_l : ∀a b,
  a <= a + b.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_lt : ∀n1 n2 m,
  n1 + n2 < m ->
  n1 < m ∧ n2 < m.
Proof.
 unfold lt.
 (* FILL IN HERE *) Admitted.

Theorem lt_S : ∀n m,
  n < m ->
  n < S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem leb_complete : ∀n m,
  leb n m = True -> n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Hint: The next one may be easiest to prove by induction on m.

Theorem leb_correct : ∀n m,
  n <= m ->
  leb n m = True.
Proof.
  (* FILL IN HERE *) Admitted.

Hint: This theorem can easily be proved without using induction.

Theorem leb_true_trans : ∀n m o,
  leb n m = True -> leb m o = True -> leb n o = True.
Proof.
  (* FILL IN HERE *) Admitted.

Exercise: 2 stars, optional (leb_iff)
Theorem leb_iff : ∀n m,
  leb n m = True ↔ n <= m.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$

Module R.

Exercise: 3 stars, recommendedM (R_provability)
We can define three-place relations, four-place relations, etc., in just the same way as binary relations. For example, consider the following three-place relation on numbers:

Inductive R : Nat -> Nat -> Nat -> Type =
   | c1 : R 0 0 0
   | c2 : ∀m n o, R m n o -> R (S m) n (S o)
   | c3 : ∀m n o, R m n o -> R m (S n) (S o)
   | c4 : ∀m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : ∀m n o, R m n o -> R n m o.

Which of the following propositions are provable?
R 1 1 2
R 2 2 6
If we dropped constructor c5 from the definition of R, would the set of provable propositions change? Briefly (1 sentence) explain your answer.
If we dropped constructor c4 from the definition of R, would the set of provable propositions change? Briefly (1 sentence) explain your answer.
(* FILL IN HERE *)
$\square$
Exercise: 3 stars, optional (R_fact)
The relation R above actually encodes a familiar function. Figure out which function; then state and prove this equivalence in Idris?

Definition fR : Nat -> Nat -> Nat
  (* REPLACE THIS LINE WITH "= _your_definition_ ." *). Admitted.

Theorem R_equiv_fR : ∀m n o, R m n o ↔ fR m n = o.
Proof.
(* FILL IN HERE *) Admitted.
$\square$

End R.

Exercise: 4 stars, advanced (subsequence)
A list is a subsequence of another list if all of the elements in the first list occur in the same order in the second list, possibly with some extra elements in between. For example,
      [1;2;3]
is a subsequence of each of the lists
      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]
but it is not a subsequence of any of the lists
      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].
Define an inductive proposition subseq on list Nat that captures what it means to be a subsequence. (Hint: You'll need three cases.)
Prove subseq_refl that subsequence is reflexive, that is, any list is a subsequence of itself.
Prove subseq_app that for any lists l1, l2, and l3, if l1 is a subsequence of l2, then l1 is also a subsequence of l2 ++ l3.
(Optional, harder) Prove subseq_trans that subsequence is transitive -- that is, if l1 is a subsequence of l2 and l2 is a subsequence of l3, then l1 is a subsequence of l3. Hint: choose your induction carefully!

(* FILL IN HERE *)
$\square$
Exercise: 2 stars, optionalM (R_provability2)
Suppose we give Idris the following definition:
    Inductive R : Nat -> list Nat -> Type =
      | c1 : R 0 []
      | c2 : ∀n l, R n l -> R (S n) (n :: l)
      | c3 : ∀n l, R (S n) l -> R n l.
Which of the following propositions are provable?
R 2 [1;0]
R 1 [1;2;1;0]
R 6 [3;2;1;0]
$\square$

Case Study: Regular Expressions
The ev property provides a simple example for illustrating inductive definitions and the basic techniques for reasoning about them, but it is not terribly exciting -- after all, it is equivalent to the two non-inductive of evenness that we had already seen, and does not seem to offer any concrete benefit over them. To give a better sense of the power of inductive definitions, we now show how to use them to model a classic concept in computer science: regular expressions.
Regular expressions are a simple language for describing strings, defined as follows:

Inductive reg_exp (T : Type) : Type =
| EmptySet : reg_exp T
| EmptyStr : reg_exp T
| Char : T -> reg_exp T
| App : reg_exp T -> reg_exp T -> reg_exp T
| Union : reg_exp T -> reg_exp T -> reg_exp T
| Star : reg_exp T -> reg_exp T.

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

Note that this definition is polymorphic: Regular expressions in reg_exp T describe strings with characters drawn from T -- that is, lists of elements of T.
(We depart slightly from standard practice in that we do not require the type T to be finite. This results in a somewhat different theory of regular expressions, but the difference is not significant for our purposes.)
We connect regular expressions and strings via the following rules, which define when a regular expression matches some string:
The expression EmptySet does not match any string.
The expression EmptyStr matches the empty string [].
The expression Char x matches the one-character string [x].
If re1 matches s1, and re2 matches s2, then App re1 re2 matches s1 ++ s2.
If at least one of re1 and re2 matches s, then Union re1 re2 matches s.
Finally, if we can write some string s as the concatenation of a sequence of strings s = s_1 ++ ... ++ s_k, and the expression re matches each one of the strings s_i, then Star re matches s.
As a special case, the sequence of strings may be empty, so Star re always matches the empty string [] no matter what re is.
We can easily translate this informal definition into an Inductive one as follows:

Inductive exp_match {T} : list T -> reg_exp T -> Type =
| MEmpty : exp_match [] EmptyStr
| MChar : ∀x, exp_match [x] (Char x)
| MApp : ∀s1 re1 s2 re2,
           exp_match s1 re1 ->
           exp_match s2 re2 ->
           exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : ∀s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : ∀re1 s2 re2,
              exp_match s2 re2 ->
              exp_match s2 (Union re1 re2)
| MStar0 : ∀re, exp_match [] (Star re)
| MStarApp : ∀s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).

Again, for readability, we can also display this definition using inference-rule notation. At the same time, let's introduce a more readable infix notation.

Notation "s =~ re" = (exp_match s re) (at level 80).

  	(MEmpty)  
[] =~ EmptyStr	
  	(MChar)  
[x] =~ Char x	
s1 =~ re1    s2 =~ re2	(MApp)  
s1 ++ s2 =~ App re1 re2	
s1 =~ re1	(MUnionL)  
s1 =~ Union re1 re2	
s2 =~ re2	(MUnionR)  
s2 =~ Union re1 re2	
  	(MStar0)  
[] =~ Star re	
s1 =~ re    s2 =~ Star re	(MStarApp)  
s1 ++ s2 =~ Star re	
Notice that these rules are not quite the same as the informal ones that we gave at the beginning of the section. First, we don't need to include a rule explicitly stating that no string matches EmptySet; we just don't happen to include any rule that would have the effect of some string matching EmptySet. (Indeed, the syntax of inductive definitions doesn't even allow us to give such a "negative rule.")
Second, the informal rules for Union and Star correspond to two constructors each: MUnionL / MUnionR, and MStar0 / MStarApp. The result is logically equivalent to the original rules but more convenient to use in Idris, since the recursive occurrences of exp_match are given as direct arguments to the constructors, making it easier to perform induction on evidence. (The exp_match_ex1 and exp_match_ex2 exercises below ask you to prove that the constructors given in the inductive declaration and the ones that would arise from a more literal transcription of the informal rules are indeed equivalent.)
Let's illustrate these rules with a few examples.

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

(Notice how the last example applies MApp to the strings [1] and [2] directly. Since the goal mentions [1; 2] instead of [1] ++ [2], Idris wouldn't be able to figure out how to split the string on its own.)
Using inversion, we can also show that certain strings do not match a regular expression:

Example reg_exp_ex3 : ¬ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

We can define helper functions to help write down regular expressions. The reg_exp_of_list function constructs a regular expression that matches exactly the list that it receives as an argument:

Fixpoint reg_exp_of_list {T} (l : list T) =
  match l with
  | [] ⇒ EmptyStr
  | x :: l' ⇒ App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

We can also prove general facts about exp_match. For instance, the following lemma shows that every string s that matches re also matches Star re.

Lemma MStar1 :
  ∀T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite ← (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(Note the use of app_nil_r to change the goal of the theorem to exactly the same shape expected by MStarApp.)
Exercise: 3 stars (exp_match_ex1)
The following lemmas show that the informal matching rules given at the beginning of the chapter can be obtained from the formal inductive definition.

Lemma empty_is_empty : ∀T (s : list T),
  ¬ (s =~ EmptySet).
Proof.
  (* FILL IN HERE *) Admitted.

Lemma MUnion' : ∀T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 ∨ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  (* FILL IN HERE *) Admitted.

The next lemma is stated in terms of the fold function from the Poly chapter: If ss : list (list T) represents a sequence of strings s1, ..., sn, then fold app ss [] is the result of concatenating them all together.

Lemma MStar' : ∀T (ss : list (list T)) (re : reg_exp T),
  (∀s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
Exercise: 4 stars (reg_exp_of_list)
Prove that reg_exp_of_list satisfies the following specification:

Lemma reg_exp_of_list_spec : ∀T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 ↔ s1 = s2.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
Since the definition of exp_match has a recursive structure, we might expect that proofs involving regular expressions will often require induction on evidence. For example, suppose that we wanted to prove the following intuitive result: If a regular expression re matches some string s, then all elements of s must occur somewhere in re. To state this theorem, we first define a function re_chars that lists all characters that occur in a regular expression:

Fixpoint re_chars {T} (re : reg_exp T) : list T =
  match re with
  | EmptySet ⇒ []
  | EmptyStr ⇒ []
  | Char x ⇒ [x]
  | App re1 re2 ⇒ re_chars re1 ++ re_chars re2
  | Union re1 re2 ⇒ re_chars re1 ++ re_chars re2
  | Star re ⇒ re_chars re
  end.

We can then phrase our theorem as follows:

Theorem in_re_match : ∀T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [
        |x'
        |s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2 re2 Hmatch IH
        |re|s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite in_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite in_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite in_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.

Something interesting happens in the MStarApp case. We obtain two induction hypotheses: One that applies when x occurs in s1 (which matches re), and a second one that applies when x occurs in s2 (which matches Star re). This is a good illustration of why we need induction on evidence for exp_match, as opposed to re: The latter would only provide an induction hypothesis for strings that match re, which would not allow us to reason about the case In x s2.

  - (* MStarApp *)
    simpl. rewrite in_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

Exercise: 4 stars (re_not_empty)
Write a recursive function re_not_empty that tests whether a regular expression matches some string. Prove that your function is correct.

Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool
  (* REPLACE THIS LINE WITH "= _your_definition_ ." *). Admitted.

Lemma re_not_empty_correct : ∀T (re : reg_exp T),
  (∃s, s =~ re) ↔ re_not_empty re = True.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
The remember Tactic
One potentially confusing feature of the induction tactic is that it happily lets you try to set up an induction over a term that isn't sufficiently general. The effect of this is to lose information (much as destruct can do), and leave you unable to complete the proof. Here's an example:

Lemma star_app: ∀T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

Just doing an inversion on H1 won't get us very far in the recursive cases. (Try it!). So we need induction. Here is a naive first attempt:

  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

But now, although we get seven cases (as we would expect from the definition of exp_match), we have lost a very important bit of information from H1: the fact that s1 matched something of the form Star re. This means that we have to give proofs for all seven constructors of this definition, even though all but two of them (MStar0 and MStarApp) are contradictory. We can still get the proof to go through for a few constructors, such as MEmpty...

  - (* MEmpty *)
    simpl. intros H. apply H.

... but most cases get stuck. For MChar, for instance, we must show that
    s2 =~ Char x' -> x' :: s2 =~ Char x',
which is clearly impossible.

  - (* MChar. Stuck... *)
Abort.

The problem is that induction over a Type hypothesis only works properly with hypotheses that are completely general, i.e., ones in which all the arguments are variables, as opposed to more complex expressions, such as Star re.
(In this respect, induction on evidence behaves more like destruct than like inversion.)
We can solve this problem by generalizing over the problematic expressions with an explicit equality:

Lemma star_app: ∀T (s1 s2 : list T) (re re' : reg_exp T),
  s1 =~ re' ->
  re' = Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

We can now proceed by performing induction over evidence directly, because the argument to the first hypothesis is sufficiently general, which means that we can discharge most cases by inverting the re' = Star re equality in the context.
This idiom is so common that Idris provides a tactic to automatically generate such equations for us, avoiding thus the need for changing the statements of our theorems.
Invoking the tactic remember e as x causes Idris to (1) replace all occurrences of the expression e by the variable x, and (2) add an equation x = e to the context. Here's how we can use it to show the above result:
Abort.

Lemma star_app: ∀T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

We now have Heqre' : re' = Star re.

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

The Heqre' is contradictory in most cases, which allows us to conclude immediately.

  - (* MEmpty *) inversion Heqre'.
  - (* MChar *) inversion Heqre'.
  - (* MApp *) inversion Heqre'.
  - (* MUnionL *) inversion Heqre'.
  - (* MUnionR *) inversion Heqre'.

The interesting cases are those that correspond to Star. Note that the induction hypothesis IH2 on the MStarApp case mentions an additional premise Star re'' = Star re', which results from the equality generated by remember.

  - (* MStar0 *)
    inversion Heqre'. intros s H. apply H.

  - (* MStarApp *)
    inversion Heqre'. rewrite H0 in IH2, Hmatch1.
    intros s2 H1. rewrite ← app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * reflexivity.
      * apply H1.
Qed.

Exercise: 4 stars (exp_match_ex2)
The MStar'' lemma below (combined with its converse, the MStar' exercise above), shows that our definition of exp_match for Star is equivalent to the informal one given previously.

Lemma MStar'' : ∀T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  ∃ss : list (list T),
    s = fold app ss []
    ∧ ∀s', In s' ss -> s' =~ re.
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
Exercise: 5 stars, advanced (pumping)
One of the first really interesting theorems in the theory of regular expressions is the so-called pumping lemma, which states, informally, that any sufficiently long string s matching a regular expression re can be "pumped" by repeating some middle section of s an arbitrary number of times to produce a new string also matching re.
To begin, we need to define "sufficiently long." Since we are working in a constructive logic, we actually need to be able to calculate, for each regular expression re, the minimum length for strings s to guarantee "pumpability."

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : Nat =
  match re with
  | EmptySet ⇒ 0
  | EmptyStr ⇒ 1
  | Char _ ⇒ 2
  | App re1 re2 ⇒
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 ⇒
      pumping_constant re1 + pumping_constant re2
  | Star _ ⇒ 1
  end.

Next, it is useful to define an auxiliary function that repeats a string (appends it to itself) some number of times.

Fixpoint napp {T} (n : Nat) (l : list T) : list T =
  match n with
  | 0 ⇒ []
  | S n' ⇒ l ++ napp n' l
  end.

Lemma napp_plus: ∀T (n m : Nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Now, the pumping lemma itself says that, if s =~ re and if the length of s is at least the pumping constant of re, then s can be split into three substrings s1 ++ s2 ++ s3 in such a way that s2 can be repeated any number of times and the result, when combined with s1 and s3 will still match re. Since s2 is also guaranteed not to be the empty string, this gives us a (constructive!) way to generate strings matching re that are as long as we like.

Lemma pumping : ∀T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  ∃s1 s2 s3,
    s = s1 ++ s2 ++ s3 ∧
    s2 ≠ [] ∧
    ∀m, s1 ++ napp m s2 ++ s3 =~ re.

To streamline the proof (which you are to fill in), the omega tactic, which is enabled by the following Require, is helpful in several places for automatically completing tedious low-level arguments involving equalities or inequalities over natural numbers. We'll return to omega in a later chapter, but feel free to experiment with it now if you like. The first case of the induction gives an example of how it is used.

Require Import Idris.omega.Omega.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. omega.
  (* FILL IN HERE *) Admitted.

End Pumping.
$\square$

Case Study: Improving Reflection
We've seen in the Logic chapter that we often need to relate boolean computations to statements in Type. But performing this conversion in the way we did it there can result in tedious proof scripts. Consider the proof of the following theorem:

Theorem filter_not_empty_In : ∀n l,
  filter (beq_nat n) l ≠ [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_nat n m) eqn:H.
    + (* beq_nat n m = True *)
      intros _. rewrite beq_nat_true_iff in H. rewrite H.
      left. reflexivity.
    + (* beq_nat n m = False *)
      intros H'. right. apply IHl'. apply H'.
Qed.

In the first branch after destruct, we explicitly apply the beq_nat_true_iff lemma to the equation generated by destructing beq_nat n m, to convert the assumption beq_nat n m = True into the assumption n = m; then we had to rewrite using this assumption to complete the case.
We can streamline this by defining an inductive proposition that yields a better case-analysis principle for beq_nat n m. Instead of generating an equation such as beq_nat n m = True, which is generally not directly useful, this principle gives us right away the assumption we really need: n = m.
We'll actually define something a bit more general, which can be used with arbitrary properties (and not just equalities):

Module FirstTry.

Inductive reflect : Type -> bool -> Type =
| ReflectT : ∀(P:Type), P -> reflect P True
| ReflectF : ∀(P:Type), ¬ P -> reflect P False.

Before explaining this, let's rearrange it a little: Since the types of both ReflectT and ReflectF begin with ∀ (P:Type), we can make the definition a bit more readable and easier to work with by making P a parameter of the whole Inductive declaration.

End FirstTry.

Inductive reflect (P : Type) : bool -> Type =
| ReflectT : P -> reflect P True
| ReflectF : ¬ P -> reflect P False.

The reflect property takes two arguments: a proposition P and a boolean b. Intuitively, it states that the property P is reflected in (i.e., equivalent to) the boolean b: P holds if and only if b = True. To see this, notice that, by definition, the only way we can produce evidence that reflect P True holds is by showing that P is True and using the ReflectT constructor. If we invert this statement, this means that it should be possible to extract evidence for P from a proof of reflect P True. Conversely, the only way to show reflect P False is by combining evidence for ¬ P with the ReflectF constructor.
It is easy to formalize this intuition and show that the two statements are indeed equivalent:

Theorem iff_reflect : ∀P b, (P ↔ b = True) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

Exercise: 2 stars, recommended (reflect_iff)
Theorem reflect_iff : ∀P b, reflect P b -> (P ↔ b = True).
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
The advantage of reflect over the normal "if and only if" connective is that, by destructing a hypothesis or lemma of the form reflect P b, we can perform case analysis on b while at the same time generating appropriate hypothesis in the two branches (P in the first subgoal and ¬ P in the second).

Lemma beq_natP : ∀n m, reflect (n = m) (beq_nat n m).
Proof.
  intros n m.
  apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

The new proof of filter_not_empty_In now goes as follows. Notice how the calls to destruct and apply are combined into a single call to destruct.
(To see this clearly, look at the two proofs of filter_not_empty_In with Idris and observe the differences in proof state at the beginning of the first case of the destruct.)

Theorem filter_not_empty_In' : ∀n l,
  filter (beq_nat n) l ≠ [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_natP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

Exercise: 3 stars, recommended (beq_natP_practice)
Use beq_natP as above to prove the following:

Fixpoint count n l =
  match l with
  | [] ⇒ 0
  | m :: l' ⇒ (if beq_nat n m then 1 else 0) + count n l'
  end.

Theorem beq_natP_practice : ∀n l,
  count n l = 0 -> ~(In n l).
Proof.
  (* FILL IN HERE *) Admitted.
$\square$
This technique gives us only a small gain in convenience for the proofs we've seen here, but using reflect consistently often leads to noticeably shorter and clearer scripts as proofs get larger. We'll see many more examples in later chapters.
The use of the reflect property was popularized by SSReflect, a Idris library that has been used to formalize important results in mathematics, including as the 4-color theorem and the Feit-Thompson theorem. The name SSReflect stands for small-scale reflection, i.e., the pervasive use of reflection to simplify small proof steps with boolean computations.

Additional Exercises
Exercise: 3 stars, recommended (nostutter)
Formulating inductive definitions of properties is an important skill you'll need in this course. Try to solve this exercise without any help at all.
We say that a list "stutters" if it repeats the same element consecutively. The property "nostutter mylist" means that mylist does not stutter. Formulate an inductive definition for nostutter. (This is different from the NoDup property in the exercise above; the sequence 1;4;1 repeats but does not stutter.)

Inductive nostutter {X:Type} : list X -> Type =
 (* FILL IN HERE *)
.
Make sure each of these tests succeeds, but feel free to change the suggested proof (in comments) if the given one doesn't work for you. Your definition might be different from ours and still be correct, in which case the examples might need a different proof. (You'll notice that the suggested proofs use a number of tactics we haven't talked about, to make them more robust to different possible ways of defining nostutter. You can probably just uncomment and use them as-is, but you can also prove each example with more basic tactics.)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
*)

Example test_nostutter_2: nostutter (@nil Nat).
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
*)

Example test_nostutter_3: nostutter [5].
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4: not (nostutter [3;1;1;4]).
(* FILL IN HERE *) Admitted.
(* 
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H1; auto. Qed.
*)
$\square$
Exercise: 4 stars, advanced (filter_challenge)
Let's prove that our definition of filter from the Poly chapter matches an abstract specification. Here is the specification, written out informally in English:
A list l is an "in-order merge" of l1 and l2 if it contains all the same elements as l1 and l2, in the same order as l1 and l2, but possibly interleaved. For example,
    [1;4;6;2;3]
is an in-order merge of
    [1;6;2]
and
    [4;3].
Now, suppose we have a set X, a function test: X->bool, and a list l of type list X. Suppose further that l is an in-order merge of two lists, l1 and l2, such that every item in l1 satisfies test and no item in l2 satisfies test. Then filter test l = l1.
Translate this specification into a Idris theorem and prove it. (You'll need to begin by defining what it means for one list to be a merge of two others. Do this with an inductive relation, not a Fixpoint.)

(* FILL IN HERE *)
$\square$
Exercise: 5 stars, advanced, optional (filter_challenge_2)
A different way to characterize the behavior of filter goes like this: Among all subsequences of l with the property that test evaluates to True on all their members, filter test l is the longest. Formalize this claim and prove it.

(* FILL IN HERE *)
$\square$
Exercise: 4 stars, optional (palindromes)
A palindrome is a sequence that reads the same backwards as forwards.
Define an inductive proposition pal on list X that captures what it means to be a palindrome. (Hint: You'll need three cases. Your definition should be based on the structure of the list; just having a single constructor like
  c : ∀l, l = rev l -> pal l
may seem obvious, but will not work very well.)
Prove (pal_app_rev) that
 ∀l, pal (l ++ rev l).
Prove (pal_rev that)
 ∀l, pal l -> l = rev l.

(* FILL IN HERE *)
$\square$
Exercise: 5 stars, optional (palindrome_converse)
Again, the converse direction is significantly more difficult, due to the lack of evidence. Using your definition of pal from the previous exercise, prove that
     ∀l, l = rev l -> pal l.

(* FILL IN HERE *)
$\square$
Exercise: 4 stars, advanced, optional (NoDup)
Recall the definition of the In property from the Logic chapter, which asserts that a value x appears at least once in a list l:

(* Fixpoint In (A : Type) (x : A) (l : list A) : Type =
   match l with
   |  => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

Your first task is to use In to define a proposition disjoint X l1 l2, which should be provable exactly when l1 and l2 are lists (with elements of type X) that have no elements in common.

(* FILL IN HERE *)

Next, use In to define an inductive proposition NoDup X l, which should be provable exactly when l is a list (with elements of type X) where every member is different from every other. For example, NoDup Nat [1;2;3;4] and NoDup bool [] should be provable, while NoDup Nat [1;2;1] and NoDup bool [True;True] should not be.

(* FILL IN HERE *)

Finally, state and prove one or more interesting theorems relating disjoint, NoDup and ++ (list append).

(* FILL IN HERE *)
$\square$
Exercise: 4 stars, advanced, optional (pigeonhole principle)
The pigeonhole principle states a basic fact about counting: if we distribute more than n items into n pigeonholes, some pigeonhole must contain at least two items. As often happens, this apparently trivial fact about numbers requires non-trivial machinery to prove, but we now have enough...
First prove an easy useful lemma.

Lemma in_split : ∀(X:Type) (x:X) (l:list X),
  In x l ->
  ∃l1 l2, l = l1 ++ x :: l2.
Proof.
  (* FILL IN HERE *) Admitted.

Now define a property repeats such that repeats X l asserts that l contains at least one repeated element (of type X).

Inductive repeats {X:Type} : list X -> Type =
  (* FILL IN HERE *)
.

Now, here's a way to formalize the pigeonhole principle. Suppose list l2 represents a list of pigeonhole labels, and list l1 represents the labels assigned to a list of items. If there are more items than labels, at least two items must have the same label -- i.e., list l1 must contain repeats.
This proof is much easier if you use the excluded_middle hypothesis to show that In is decidable, i.e., ∀ x l, (In x l) ∨ ¬ (In x l). However, it is also possible to make the proof go through without assuming that In is decidable; if you manage to do this, you will not need the excluded_middle hypothesis.

Theorem pigeonhole_principle: ∀(X:Type) (l1 l2:list X),
   excluded_middle ->
   (∀x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
  (* FILL IN HERE *) Admitted.
$\square$
Index
