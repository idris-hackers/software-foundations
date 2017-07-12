= Induction: Proof by Induction

> module Induction

First, we import all of our definitions from the previous chapter.

> import Basics

Next, we import the following `Prelude` modules, since we'll be dealing with
natural numbers.

> import Prelude.Interfaces
> import Prelude.Nat

For `import Basics` to work, you first need to use `idris` to compile
`Basics.lidr` into `Basics.ibc`. This is like making a .class file from a .java
file, or a .o file from a .c file. There are at least two ways to do it:

  - In your editor with an Idris plugin, e.g. [Emacs][idris-mode]:

    Open `Basics.lidr`. Evaluate `idris-load-file`.

    There exists similar support for [Vim][idris-vim], [Sublime
    Text][idris-sublime] and [Visual Studio Code][idris-vscode] as well.

    [idris-mode]: https://github.com/idris-hackers/idris-mode
    [idris-vim]: https://github.com/idris-hackers/idris-vim
    [idris-sublime]: https://github.com/idris-hackers/idris-sublime
    [idris-vscode]: https://github.com/zjhmale/vscode-idris

  - From the command line:

    Run \mintinline[]{sh}{idris --check --total --noprelude src/Basics.lidr}.

    Refer to the Idris man page (or \mintinline[]{sh}{idris --help} for
    descriptions of the flags.


== Proof by Induction

We proved in the last chapter that `0` is a neutral element for `+` on the left
using an easy argument based on simplification. The fact that it is also a
neutral element on the _right_...

```coq
Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.
```

... cannot be proved in the same simple way in Coq, but as we saw in `Basics`,
Idris's `Refl` just works.

To prove interesting facts about numbers, lists, and other inductively defined
sets, we usually need a more powerful reasoning principle: _induction_.

Recall (from high school, a discrete math course, etc.) the principle of
induction over natural numbers: If `p n` is some proposition involving a natural
number `n` and we want to show that `p` holds for _all_ numbers `n`, we can
reason like this:

  - show that `p Z` holds;
  - show that, for any `k`, if `p k` holds, then so does `p (S k)`;
  - conclude that `p n` holds for all `n`.

In Idris, the steps are the same and can often be written as function clauses by
case splitting. Here's how this works for the theorem at hand.

> plus_n_Z : (n : Nat) -> n = n + 0
> plus_n_Z  Z    = Refl
> plus_n_Z (S k) =
>   let inductiveHypothesis = plus_n_Z k in
>     rewrite inductiveHypothesis in Refl

In the first clause, `n` is replaced by `Z` and the goal becomes `0 = 0`, which
follows by `Refl`exivity. In the second, `n` is replaced by `S k` and the goal
becomes `S k = S (plus k 0)`. Then we define the inductive hypothesis, `k =
k + 0`, which can be written as `plus_n_Z k`, and the goal follows from it.

> minus_diag : (n : Nat) -> minus n n = 0
> minus_diag  Z    = Refl
> minus_diag (S k) = minus_diag k


=== Exercise: 2 stars, recommended (basic_induction)

Prove the following using induction. You might need previously proven results.

> mult_0_r : (n : Nat) -> n * 0 = 0
> mult_0_r n = ?mult_0_r_rhs

> plus_n_Sm : (n, m : Nat) -> S (n + m) = n + (S m)
> plus_n_Sm n m = ?plus_n_Sm_rhs

> plus_comm : (n, m : Nat) -> n + m = m + n
> plus_comm n m = ?plus_comm_rhs

> plus_assoc : (n, m, p : Nat) -> n + (m + p) = (n + m) + p
> plus_assoc n m p = ?plus_assoc_rhs

$\square$


=== Exercise: 2 stars (double_plus)

Consider the following function, which doubles its argument:

> double : (n : Nat) -> Nat
> double  Z    = Z
> double (S k) = S (S (double k))

Use induction to prove this simple fact about `double`:

> double_plus : (n : Nat) -> double n = n + n
> double_plus n = ?double_plus_rhs

$\square$


=== Exercise: 2 stars, optional (evenb_S)

One inconvenient aspect of our definition of `evenb n` is that it may need to
perform a recursive call on `n - 2`. This makes proofs about `evenb n` harder
when done by induction on `n`, since we may need an induction hypothesis about
`n - 2`. The following lemma gives a better characterization of `evenb (S n)`:

> evenb_S : (n : Nat) -> evenb (S n) = negb (evenb n)
> evenb_S n = ?evenb_S_rhs

$\square$


== Proofs Within Proofs

In Coq, as in informal mathematics, large proofs are often broken into a
sequence of theorems, with later proofs referring to earlier theorems. But
sometimes a proof will require some miscellaneous fact that is too trivial and
of too little general interest to bother giving it its own top-level name. In
such cases, it is convenient to be able to simply state and prove the needed
"sub-theorem" right at the point where it is used. The `assert` tactic allows us
to do this. For example, our earlier proof of the `mult_0_plus` theorem referred
to a previous theorem named `plus_Z_n`. We could instead use `assert` to state
and prove `plus_Z_n` in-line:

> mult_0_plus' : (n, m : Nat) -> (0 + n) * m = n * m
> mult_0_plus' n m = Refl

The `assert` tactic introduces two sub-goals. The first is the assertion itself;
by prefixing it with `H:` we name the assertion `H`. (We can also name the
assertion with `as` just as we did above with `destruct` and `induction`, i.e.,
`assert (0 + n = n) as H`.) Note that we surround the proof of this assertion
with curly braces `{ ... }`, both for readability and so that, when using Coq
interactively, we can see more easily when we have finished this sub-proof. The
second goal is the same as the one at the point where we invoke `assert` except
that, in the context, we now have the assumption `H` that `0 + n = n`. That is,
`assert` generates one subgoal where we must prove the asserted fact and a
second subgoal where we can use the asserted fact to make progress on whatever
we were trying to prove in the first place.

The `assert` tactic is handy in many sorts of situations. For example, suppose
we want to prove that `(n + m) + (p + q) = (m + n) + (p + q)`. The only
difference between the two sides of the `=` is that the arguments `m` and `n` to
the first inner `+` are swapped, so it seems we should be able to use the
commutativity of addition (`plus_comm`) to rewrite one into the other. However,
the `rewrite` tactic is a little stupid about _where_ it applies the rewrite.
There are three uses of `+` here, and it turns out that doing `rewrite ->
plus_comm` will affect only the _outer_ one...

```idris
plus_rearrange_firsttry : (n, m, p, q : Nat) ->
                          (n + m) + (p + q) = (m + n) + (p + q)
plus_rearrange_firsttry n m p q = rewrite plus_comm in Refl
```
```
When checking right hand side of plus_rearrange_firsttry with expected type
        n + m + (p + q) = m + n + (p + q)

_ does not have an equality type ((n1 : Nat) ->
(n1 : Nat) -> plus n1 m1 = plus m1 n1)
```

To get `plus_comm` to apply at the point where we want it to, we can introduce a
local lemma using the `where` keyword stating that `n + m = m + n` (for the
particular `m` and `n` that we are talking about here), prove this lemma using
`plus_comm`, and then use it to do the desired rewrite.

> plus_rearrange : (n, m, p, q : Nat) ->
>                  (n + m) + (p + q) = (m + n) + (p + q)
> plus_rearrange n m p q = rewrite plus_rearrange_lemma n m in Refl
>   where
>   plus_rearrange_lemma : (n, m : Nat) -> n + m = m + n
>   plus_rearrange_lemma = plus_comm

== More Exercises

=== Exercise: 3 stars, recommended (mult_comm)

Use `rewrite` to help prove this theorem. You shouldn't need to use induction on
`plus_swap`.

> plus_swap : (n, m, p : Nat) -> n + (m + p) = m + (n + p)
> plus_swap n m p = ?plus_swap_rhs

Now prove commutativity of multiplication. (You will probably need to define and
prove a separate subsidiary theorem to be used in the proof of this one. You may
find that `plus_swap` comes in handy.)

> mult_comm : (m, n : Nat) -> m * n = n * m
> mult_comm m n = ?mult_comm_rhs

$\square$


=== Exercise: 3 stars, optional (more_exercises)

Take a piece of paper. For each of the following theorems, first _think_ about
whether (a) it can be proved using only simplification and rewriting, (b) it
also requires case analysis (`destruct`), or (c) it also requires induction.
Write down your prediction. Then fill in the proof. (There is no need to turn in
your piece of paper; this is just to encourage you to reflect before you hack!)

> leb_refl : (n : Nat) -> True = leb n n
> leb_refl n = ?leb_refl_rhs

> zero_nbeq_S : (n : Nat) -> beq_nat 0 (S n) = False
> zero_nbeq_S n = ?zero_nbeq_S_rhs

> andb_false_r : (b : Bool) -> andb b False = False
> andb_false_r b = ?andb_false_r_rhs

> plus_ble_compat_l : (n, m, p : Nat) ->
>                     leb n m = True -> leb (p + n) (p + m) = True
> plus_ble_compat_l n m p prf = ?plus_ble_compat_l_rhs

> S_nbeq_0 : (n : Nat) -> beq_nat (S n) 0 = False
> S_nbeq_0 n = ?S_nbeq_0_rhs

> mult_1_l : (n : Nat) -> 1 * n = n
> mult_1_l n = ?mult_1_l_rhs

> all3_spec : (b, c : Bool) ->
>             orb (andb b c)
>                 (orb (negb b)
>                      (negb c))
>             = True
> all3_spec b c = ?all3_spec_rhs

> mult_plus_distr_r : (n, m, p : Nat) -> (n + m) * p = (n * p) + (m * p)
> mult_plus_distr_r n m p = ?mult_plus_distr_r_rhs

> mult_assoc : (n, m, p : Nat) -> n * (m * p) = (n * m) * p
> mult_assoc n m p = ?mult_assoc_rhs

$\square$


=== Exercise: 2 stars, optional (beq_nat_refl)

Prove the following theorem. (Putting the `True` on the left-hand side of the
equality may look odd, but this is how the theorem is stated in the Coq standard
library, so we follow suit. Rewriting works equally well in either direction, so
we will have no problem using the theorem no matter which way we state it.)

> beq_nat_refl : (n : Nat) -> True = beq_nat n n
> beq_nat_refl n = ?beq_nat_refl_rhs

$\square$


=== Exercise: 2 stars, optional (plus_swap')

The `replace` tactic allows you to specify a particular subterm to rewrite and
what you want it rewritten to: `replace (t) with (u)` replaces (all copies of)
expression `t` in the goal by expression `u`, and generates `t = u` as an
additional subgoal. This is often useful when a plain `rewrite` acts on the
wrong part of the goal.

Use the `replace` tactic to do a proof of `plus_swap'`, just like `plus_swap`
but without needing `assert (n + m = m + n)`.

> plus_swap' : (n, m, p : Nat) -> n + (m + p) = m + (n + p)
> plus_swap' n m p = ?plus_swap'_rhs

$\square$


=== Exercise: 3 stars, recommended (binary_commute)

Recall the `incr` and `bin_to_nat` functions that you wrote for the `binary`
exercise in the `Basics` chapter. Prove that the following diagram commutes:

           bin --------- incr -------> bin
            |                           |
        bin_to_nat                  bin_to_nat
            |                           |
            v                           v
           nat ---------- S ---------> nat

That is, incrementing a binary number and then converting it to a (unary)
natural number yields the same result as first converting it to a natural number
and then incrementing. Name your theorem `bin_to_nat_pres_incr` ("pres" for
"preserves").

Before you start working on this exercise, please copy the definitions from your
solution to the `binary` exercise here so that this file can be graded on its
own. If you find yourself wanting to change your original definitions to make
the property easier to prove, feel free to do so!

$\square$


=== Exercise: 5 stars, advanced (binary_inverse)

This exercise is a continuation of the previous exercise about binary numbers.
You will need your definitions and theorems from there to complete this one.

(a) First, write a function to convert natural numbers to binary numbers. Then
    prove that starting with any natural number, converting to binary, then
    converting back yields the same natural number you started with.

(b) You might naturally think that we should also prove the opposite direction:
    that starting with a binary number, converting to a natural, and then back
    to binary yields the same number we started with. However, this is not true!
    Explain what the problem is.

(c) Define a "direct" normalization function -- i.e., a function `normalize`
    from binary numbers to binary numbers such that, for any binary number b,
    converting to a natural and then back to binary yields `(normalize b)`.
    Prove it. (Warning: This part is tricky!)

Again, feel free to change your earlier definitions if this helps here.

$\square$
