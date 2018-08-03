= ImpCEvalFun : Evaluation Function for Imp 

> module ImpCEvalFun

We saw in the `Imp` chapter how a naive approach to defining a function
representing evaluation for Imp runs into difficulties. There, we adopted the
solution of changing from a functional to a relational definition of evaluation.
In this optional chapter, we consider strategies for getting the functional
approach to work.

> import Logic
> import Maps
> import Imp

> %access public export
> %default total

== A Broken Evaluator

Here was our first try at an evaluation function for commands, omitting
\idr{WHILE}. 

> ceval_step1 : (st : State) -> (c : Com) -> State
> ceval_step1 st CSkip = st
> ceval_step1 st (CAss l a1) = t_update l (aeval st a1) st
> ceval_step1 st (CSeq c1 c2) =
>   let st' = ceval_step1 st c1
>   in ceval_step1 st' c2
> ceval_step1 st (CIf b c1 c2) =
>   if beval st b
>     then ceval_step1 st c1
>     else ceval_step1 st c2
> ceval_step1 st (CWhile b c) = st   -- bogus

As we remarked in chapter `Imp`, in a traditional functional programming
language like ML or Haskell we could write the WHILE case as follows:

```idris
...
ceval_step1 st (CWhile b c) =
  if (beval st b)
    then ceval_step1 st (CSeq c $ CWhile b c)
    else st
```

Idris doesn't accept such a definition (\idr{ImpCEvalFun.ceval_step1 is possibly 
not total due to recursive path ImpCEvalFun.ceval_step1 --> 
ImpCEvalFun.ceval_step1 --> ImpCEvalFun.ceval_step1}) because the function we 
want to define is not guaranteed to terminate. Indeed, the changed 
\idr{ceval_step1} function applied to the \idr{loop} program from `Imp.lidr` 
would never terminate. Since Idris is not just a functional programming 
language, but also a consistent logic, any potentially non-terminating function 
needs to be rejected. Here is an invalid(!) Idris program showing what would go 
wrong if Idris allowed non-terminating recursive functions: 

```idris
loop_false : (n : Nat) -> Void 
loop_false n = loop_false n
```

That is, propositions like \idr{Void} would become provable (e.g.,
\idr{loop_false 0} would be a proof of \idr{Void}), which would be a disaster
for Idris's logical consistency.

Thus, because it doesn't terminate on all inputs, the full version of
\idr{ceval_step1} cannot be written in Idris -- at least not without one
additional trick... 

== A Step-Indexed Evaluator

The trick we need is to pass an _additional_ parameter to the evaluation
function that tells it how long to run. Informally, we start the evaluator with
a certain amount of "gas" in its tank, and we allow it to run until either it
terminates in the usual way _or_ it runs out of gas, at which point we simply
stop evaluating and say that the final result is the empty memory. (We could
also say that the result is the current state at the point where the evaluator
runs out fo gas -- it doesn't really matter because the result is going to be
wrong in either case!) 

> ceval_step2 : (st : State) -> (c : Com) -> (i : Nat) -> State
> ceval_step2 _ _ Z = empty_state
> ceval_step2 st CSkip (S i') = st
> ceval_step2 st (CAss l a1) (S i') = t_update l (aeval st a1) st
> ceval_step2 st (CSeq c1 c2) (S i') = 
>   let st' = ceval_step2 st c1 i'
>   in ceval_step2 st' c2 i'
> ceval_step2 st (CIf b c1 c2) (S i') = 
>   if beval st b
>     then ceval_step2 st c1 i'
>     else ceval_step2 st c2 i'
> ceval_step2 st c@(CWhile b1 c1) (S i') = 
>   if (beval st b1)
>     then let st' = ceval_step2 st c1 i' in 
>          ceval_step2 st' c i'
>     else st

_Note_: It is tempting to think that the index \idr{i} here is counting the
"number of steps of evaluation." But if you look closely you'll see that this
is not the case: for example, in the rule for sequencing, the same \idr{i} is
passed to both recursive calls. Understanding the exact way that \idr{i} is
treated will be important in the proof of \idr{ceval__ceval_step}, which is
given as an exercise below.

One thing that is not so nice about this evaluator is that we can't tell, from
its result, whether it stopped because the program terminated normally or
because it ran out of gas.  Our next version returns an \idr{Maybe State}
instead of just a \idr{State}, so that we can distinguish between normal and
abnormal termination.

> ceval_step3 : (st : State) -> (c : Com) -> (i : Nat) -> Maybe State
> ceval_step3 _ _ Z = Nothing
> ceval_step3 st CSkip (S i') = Just st
> ceval_step3 st (CAss l a1) (S i') = Just $ t_update l (aeval st a1) st
> ceval_step3 st (CSeq c1 c2) (S i') = 
>   case ceval_step3 st c1 i' of
>     Just st' => ceval_step3 st' c2 i'
>     Nothing => Nothing
> ceval_step3 st (CIf b c1 c2) (S i') = 
>   if beval st b
>     then ceval_step3 st c1 i'
>     else ceval_step3 st c2 i'
> ceval_step3 st c@(CWhile b1 c1) (S i') = 
>   if (beval st b1)
>     then case ceval_step3 st c1 i' of 
>            Just st' => ceval_step3 st' c i'
>            Nothing => Nothing
>     else Just st

We can improve the readability of this version by using the fact that /idr{Maybe} forms a monad to hide the plumbing involved in repeatedly matching against optional
states.

```idris
Monad Maybe where
    Nothing  >>= k = Nothing
    (Just x) >>= k = k x
```

> ceval_step : (st : State) -> (c : Com) -> (i : Nat) -> Maybe State
> ceval_step _ _ Z = Nothing
> ceval_step st CSkip (S i') = Just st
> ceval_step st (CAss l a1) (S i') = Just $ t_update l (aeval st a1) st
> ceval_step st (CSeq c1 c2) (S i') = 
>   do st' <- ceval_step st c1 i'
>      ceval_step st' c2 i'
> ceval_step st (CIf b c1 c2) (S i') = 
>   if beval st b
>     then ceval_step st c1 i'
>     else ceval_step st c2 i'
> ceval_step st c@(CWhile b1 c1) (S i') = 
>   if (beval st b1)
>     then do st' <- ceval_step st c1 i'
>             ceval_step st' c i'
>     else Just st

> test_ceval : (st : State) -> (c : Com) -> Maybe (Nat, Nat, Nat)
> test_ceval st c  = case ceval_step st c 500 of
>   Nothing => Nothing
>   Just st => Just (st X, st Y, st Z)

\todo[inline]{Syntax sugar for IF breaks down here}

```idris 
λΠ> test_ceval Imp.empty_state (CSeq (X ::= ANum 2) (CIf (BLe (AId X) (ANum 1)) (Y ::= ANum 3) (Z ::= ANum 4)))
Just (2, 0, 4) : Maybe (Nat, Nat, Nat)
```

==== Exercise: 2 stars, recommended (pup_to_n)

Write an Imp program that sums the numbers from \idr{1} to \idr{X} (inclusive:
\idr{1 + 2 + ... + X}) in the variable \idr{Y}. Make sure your solution
satisfies the test that follows.

> pup_to_n : Com
> pup_to_n = ?pup_to_n_rhs

> pup_to_n_1 : test_ceval (t_update X 5 $ Imp.empty_state) ImpCEvalFun.pup_to_n = Just (0, 15, 0)
> pup_to_n_1 = ?pup_to_n_1 -- replace with Refl when done

$\square$


==== Exercise: 2 stars, optional (peven) 

Write a \idr{While} program that sets \idr{Z} to \idr{0} if \idr{X} is even and
sets \idr{Z} to \idr{1} otherwise. Use \idr{test_ceval} to test your program.

> -- FILL IN HERE

$\square$

== Relational vs. Step-Indexed Evaluation

As for arithmetic and boolean expressions, we'd hope that the two alternative
definitions of evaluation would actually amount to the same thing in the end.
This section shows that this is the case. 

> ceval_step__ceval : (c : Com) -> (st, st' : State) -> (i ** ceval_step st c i = Just st') -> c / st \\ st'
> ceval_step__ceval c st st' (Z ** prf) = absurd prf
> ceval_step__ceval CSkip st st (S i ** Refl) = E_Skip
> ceval_step__ceval (CAss l a) st st' (S i ** prf) = 
>  rewrite sym $ justInjective prf in 
>  E_Ass {n=aeval st a} Refl
> ceval_step__ceval (CSeq c1 c2) st st' (S i ** prf) with (ceval_step st c1 i) proof c1prf
>   ceval_step__ceval (CSeq c1 c2) st st' (S i ** prf) | Just st1 = 
>     E_Seq (ceval_step__ceval c1 st st1 (i**sym c1prf))
>           (ceval_step__ceval c2 st1 st' (i**prf))
>   ceval_step__ceval (CSeq c1 c2) st st' (S i ** prf) | Nothing = absurd prf
> ceval_step__ceval (CIf b c1 c2) st st' (S i ** prf) with (beval st b) proof bprf
>   ceval_step__ceval (CIf b c1 c2) st st' (S i ** prf) | True  = 
>     E_IfTrue (sym bprf) (ceval_step__ceval c1 st st' (i**prf))
>   ceval_step__ceval (CIf b c1 c2) st st' (S i ** prf) | False = 
>     E_IfFalse (sym bprf) (ceval_step__ceval c2 st st' (i**prf))
> ceval_step__ceval (CWhile b c) st st' (S i ** prf) with (beval st b) proof bprf
>   ceval_step__ceval (CWhile b c) st st' (S i ** prf) | True with (ceval_step st c i) proof cprf
>     ceval_step__ceval (CWhile b c) st st' (S i ** prf) | True | Just st1 =
>       E_WhileLoop (sym bprf) (ceval_step__ceval c st st1 (i**sym cprf)) 

\todo[inline]{Idris can't see sigma is decreasing, use WellFounded here?}

>                              (assert_total $ ceval_step__ceval (CWhile b c) st1 st' (i**prf))       
>     ceval_step__ceval (CWhile b c) st st' (S i ** prf) | True | Nothing = absurd prf
>   ceval_step__ceval (CWhile b c) st st (S i ** Refl) | False = E_WhileEnd (sym bprf)


==== Exercise: 4 stars (ceval_step__ceval_inf)

Write an informal proof of \idr{ceval_step__ceval}, following the usual
template. (The template for case analysis on an inductively defined value should
look the same as for induction, except that there is no induction hypothesis.)
Make your proof communicate the main ideas to a human reader; do not simply
transcribe the steps of the formal proof.

> -- FILL IN HERE

$\square$

> ceval_step_more : (i1, i2 : Nat) -> (st, st' : State) -> (c : Com) -> LTE i1 i2 -> ceval_step st c i1 = Just st' 
>                -> ceval_step st c i2 = Just st'
> ceval_step_more Z i2 st st' c lte prf = absurd prf
> ceval_step_more (S i1) Z st st' c lte prf = absurd lte
> ceval_step_more (S i1) (S i2) st st' CSkip lte prf = prf
> ceval_step_more (S i1) (S i2) st st' (CAss l a) lte prf = prf
> ceval_step_more (S i1) (S i2) st st' (CSeq c1 c2) lte prf with (ceval_step st c1 i1) proof cprf
>   ceval_step_more (S i1) (S i2) st st' (CSeq c1 c2) lte prf | Just st1 = 
>     rewrite ceval_step_more i1 i2 st st1 c1 (fromLteSucc lte) (sym cprf) in 
>     ceval_step_more i1 i2 st1 st' c2 (fromLteSucc lte) prf
>   ceval_step_more (S i1) (S i2) st st' (CSeq c1 c2) lte prf | Nothing = absurd prf
> ceval_step_more (S i1) (S i2) st st' (CIf b c1 c2) lte prf with (beval st b) proof bprf
>   ceval_step_more (S i1) (S i2) st st' (CIf b c1 c2) lte prf | True = 
>     ceval_step_more i1 i2 st st' c1 (fromLteSucc lte) prf
>   ceval_step_more (S i1) (S i2) st st' (CIf b c1 c2) lte prf | False = 
>     ceval_step_more i1 i2 st st' c2 (fromLteSucc lte) prf
> ceval_step_more (S i1) (S i2) st st' (CWhile b c) lte prf with (beval st b) 
>   ceval_step_more (S i1) (S i2) st st' (CWhile b c) lte prf | True with (ceval_step st c i1) proof cprf
>     ceval_step_more (S i1) (S i2) st st' (CWhile b c) lte prf | True | Just st1 = 
>       rewrite ceval_step_more i1 i2 st st1 c (fromLteSucc lte) (sym cprf) in 
>       ceval_step_more i1 i2 st1 st' (CWhile b c) (fromLteSucc lte) prf
>     ceval_step_more (S i1) (S i2) st st' (CWhile b c) lte prf | True | Nothing = absurd prf
>   ceval_step_more (S i1) (S i2) st st' (CWhile b c) lte prf | False = prf


==== Exercise: 3 stars, recommended (ceval__ceval_step)

Finish the following proof. You'll need \idr{ceval_step_more} in a few places,
as well as some basic facts about \idr{LTE} and \idr{S}. 

> ceval__ceval_step : (c : Com) -> (st, st' : State) -> (c / st \\ st') -> (i ** ceval_step st c i = Just st')
> ceval__ceval_step c st st' prf = ?ceval__ceval_step_rhs 

$\square$

> ceval_and_ceval_step_coincide : (c : Com) -> (st, st' : State) -> (c / st \\ st') <-> (i ** ceval_step st c i = Just st')
> ceval_and_ceval_step_coincide c st st' = (ceval__ceval_step c st st', ceval_step__ceval c st st')


== Determinism of Evaluation Again 

Using the fact that the relational and step-indexed definition of evaluation are
the same, we can give a slicker proof that the evaluation _relation_ is
deterministic. 

> ceval_deterministic' : (c : Com) -> (st, st1, st2 : State) -> (c / st \\ st1) -> (c / st \\ st2) -> st1 = st2
> ceval_deterministic' c st st1 st2 prf1 prf2 = 
>   let 
>     (i1**e1) = ceval__ceval_step c st st1 prf1 
>     (i2**e2) = ceval__ceval_step c st st2 prf2 
>     plus1 = ceval_step_more i1 (i1+i2) st st1 c (lteAddRight i1) e1
>     plus2 = ceval_step_more i2 (i1+i2) st st2 c (rewrite plusCommutative i1 i2 in lteAddRight i2) e2
>     in     
>   justInjective $ trans (sym plus1) plus2
