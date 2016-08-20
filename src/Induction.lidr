---
pandoc-minted:
  language: idris
---

= Induction: Proof by Induction

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

    There exists similar support for [Vim][idris-vim] and [Sublime
    Text][idris-sublime] as well.

    [idris-mode]: https://github.com/idris-hackers/idris-mode
    [idris-vim]: https://github.com/idris-hackers/idris-vim
    [idris-sublime]: https://github.com/idris-hackers/idris-sublime

  - From the command line:

    Run \mintinline[]{sh}{idris --check --total --noprelude src/Basics.lidr}.

    Refer to the Idris man page (or \mintinline[]{sh}{idris --help} for
    descriptions of the flags.


== Proof by Induction

We proved in the last chapter that `0` is a netural element for `+` on the left
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
  - show that, for any `n'`, if `p in'` holds, then so does `p (S n')`;
  - conclude that `p n` holds for all `n`.

In Idris, the steps are the same and can often be written as function clauses by
case splitting. Here's how this works for the theorem at hand.

> plus_n_Z : (n : Nat) -> n = n + 0
> plus_n_Z  Z     = Refl
> plus_n_Z (S n') =
>   let inductiveHypothesis = plus_n_Z n' in
>     rewrite inductiveHypothesis in Refl

In the first clause, `n` is replaced by `Z` and the goal becomes `0 = 0`, which
follows by `Refl`exivity. In the second, `n` is replaced by `S n'` and the goal
becomes `S n' = S (plus n' 0)`. Then we define the inductive hypothesis, `n' =
n' + 0`, which can be written as `plus_n_Z n'`, and the goal follows from it.

> minus_diag : (n : Nat) -> minus n n = 0
> minus_diag  Z     = Refl
> minus_diag (S n') = minus_diag n'


=== Exercise: 2 stars, recommended (basic_induction)

Prove the following using induction. You might need previously proven results.

> mult_0_r : (n : Nat) -> n * 0 = 0
> mult_0_r n = ?mult_0_r_rhs

> plus_n_Sm : (n, m : Nat) -> S (n + m) = n + (S m)
> plus_n_Sm n m = ?plus_n_Sm_rhs

> plus_comm : (n, m : Nat) -> n + m = m + n
> plus_comm n m = ?plus_comm_rhs

$\square$
