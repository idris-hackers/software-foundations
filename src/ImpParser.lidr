= ImpParser: Lexing and Parsing in Idris

> module ImpParser
>

The development of the Imp language in `Imp.lidr` completely ignores issues of
concrete syntax -- how an ascii string that a programmer might write gets
translated into abstract syntax trees defined by the datatypes \idr{AExp},
\idr{BExp}, and \idr{Com}.  In this chapter, we illustrate how the rest of the
story can be filled in by building a simple lexical analyzer and parser using
Idris's functional programming facilities.

It is not important to understand all the details here (and accordingly, the
explanations are fairly terse and there are no exercises).  The main point is
simply to demonstrate that it can be done.  You are invited to look through the
code -- most of it is not very complicated, though the parser relies on some
"monadic" programming idioms that may require a little work to make out -- but
most readers will probably want to just skim down to the Examples section at the
very end to get the punchline.

> import Maps
> import Imp
>

== Internals

=== Lexical Analysis

> data Chartype = White | Alpha | Digit | Other
>
> classifyChar : (c : Char) -> Chartype
> classifyChar c =
>   if isSpace c then
>     White
>   else if isAlpha c then
>     Alpha
>   else if isDigit c then
>     Digit
>   else
>     Other
>
> Token : Type
> Token = String
>
> tokenizeHelper : (cls : Chartype) -> (acc, xs : List Char) -> List (List Char)
> tokenizeHelper cls acc xs =
>   case xs of
>     []       => tk
>     (x::xs') =>
>       case (cls, classifyChar x, x) of
>         (_, _, '(')       =>
>           tk ++ ['('] :: (tokenizeHelper Other [] xs')
>         (_, _, ')')       =>
>           tk ++ [')'] :: (tokenizeHelper Other [] xs')
>         (_, White, _)     =>
>           tk ++ (tokenizeHelper White [] xs')
>         (Alpha, Alpha, x) =>
>           tokenizeHelper Alpha (x::acc) xs'
>         (Digit, Digit, x) =>
>           tokenizeHelper Digit (x::acc) xs'
>         (Other, Other, x) =>
>           tokenizeHelper Other (x::acc) xs'
>         (_, tp, x)        =>
>           tk ++ (tokenizeHelper tp [x] xs')
>  where
>   tk : List (List Char)
>   tk = case acc of
>          []     => []
>          (_::_) => [reverse acc]
>
> tokenize : (s : String) -> List String
> tokenize s = map pack (tokenizeHelper White [] (unpack s))
>
> tokenizeEx1 : tokenize "abc12==3  223*(3+(a+c))" = ["abc","12","==","3","223","*","(","3","+","(","a","+","c",")",")"]
> tokenizeEx1 = Refl
>

=== Parsing

==== Options With Errors

An `option` type with error messages:

> data OptionE : (x : Type) -> Type where
>   SomeE : x -> OptionE x
>   NoneE : String -> OptionE x
>

Some interface instances to make writing nested match-expressions on `OptionE`
more convenient.

\todo[inline]{Explain these/link to Haskell etc?}

> Functor OptionE where
>   map f (SomeE x)   = SomeE (f x)
>   map _ (NoneE err) = NoneE err
>
> Applicative OptionE where
>   pure = SomeE
>   (SomeE f) <*> (SomeE x) = SomeE (f x)
>   (SomeE _) <*> (NoneE e) = NoneE e
>   (NoneE e) <*> _         = NoneE e
>
> Alternative OptionE where
>   empty = NoneE ""
>   (SomeE x) <|> _ = SomeE x
>   (NoneE _) <|> v = v
>
> Monad OptionE where
>   (NoneE e) >>= _ = NoneE e
>   (SomeE x) >>= k = k x
>

==== Generic Combinators for Building Parsers

> Parser : (t : Type) -> Type
> Parser t = List Token -> OptionE (t, List Token)
>
> manyHelper : (p : Parser t) -> (acc : List t) -> (steps : Nat) -> Parser (List t)
> manyHelper p acc Z _ = NoneE "Too many recursive calls"
> manyHelper p acc (S steps') xs with (p xs)
>  | NoneE _        = SomeE (reverse acc, xs)
>  | SomeE (t', xs') = manyHelper p (t'::acc) steps' xs'
>

A (step-indexed) parser that expects zero or more `p`s:

> many : (p : Parser t) -> (steps : Nat) -> Parser (List t)
> many p steps = manyHelper p [] steps
>

A parser that expects a given token, followed by `p`:

> firstExpect : (a : Token) -> (p : Parser t) -> Parser t
> firstExpect a p (x::xs) = if x == a then p xs else NoneE ("Expected '" ++ a ++ "'")
> firstExpect a _ [] = NoneE ("Expected '" ++ a ++ "'")
>

A parser that expects a particular token:

> expect : (t : Token) -> Parser ()
> expect t = firstExpect t (\xs => SomeE ((), xs))
>

==== A Recursive-Descent Parser for Imp

Identifiers:

> parseIdentifier : Parser Id
> parseIdentifier [] = NoneE "Expected identifier"
> parseIdentifier (x::xs) =
>   if all isLower (unpack x)
>     then SomeE (MkId x, xs)
>     else NoneE ("Illegal identifier:'" ++ x ++ "'")
>

Numbers:

> parseNumber : Parser Nat
> parseNumber [] = NoneE "Expected number"
> parseNumber (x::xs) =
>   if all isDigit (unpack x)
>     then SomeE (foldl (\n, d => 10 * n + (cast (ord d - ord '0'))) 0 (unpack x), xs)
>     else NoneE "Expected number"
>

Parse arithmetic expressions

> mutual
>   parsePrimaryExp : (steps : Nat) -> Parser AExp
>   parsePrimaryExp Z _ = NoneE "Too many recursive calls"
>   parsePrimaryExp (S steps') xs =
>     (do (i, rest) <- parseIdentifier xs
>         pure (AId i, rest))
>     <|>
>     (do (n, rest) <- parseNumber xs
>         pure (ANum n, rest))
>     <|>
>     (do (e, rest)  <- firstExpect "(" (parseSumExp steps') xs
>         (u, rest') <- expect ")" rest
>         pure (e, rest'))
>
>   parseProductExp : (steps : Nat) -> Parser AExp
>   parseProductExp Z _ = NoneE "Too many recursive calls"
>   parseProductExp (S steps') xs =
>     do (e, rest) <- parsePrimaryExp steps' xs
>        (es, rest') <- many (firstExpect "*" (parsePrimaryExp steps')) steps' rest
>        pure (foldl AMult e es, rest')
>
>   parseSumExp : (steps : Nat) -> Parser AExp
>   parseSumExp Z _ = NoneE "Too many recursive calls"
>   parseSumExp (S steps') xs =
>     do (e, rest) <- parseProductExp steps' xs
>        (es, rest') <- many psum steps' rest
>        pure (foldl (\e0, term =>
>                      case term of
>                        (True,  e) => APlus e0 e
>                        (False, e) => AMinus e0 e
>                    ) e es, rest')
>     where
>     psum : Parser (Bool, AExp)
>     psum xs =
>       let p = parseProductExp steps' in
>       (do (e, r) <- firstExpect "+" p xs
>           pure ((True, e), r))
>       <|>
>       (do (e, r) <- firstExpect "-" p xs
>           pure ((False, e), r))
>
> parseAExp : (steps : Nat) -> Parser AExp
> parseAExp = parseSumExp
>

Parsing boolean expressions:

> mutual
>   parseAtomicExp : (steps : Nat) -> Parser BExp
>   parseAtomicExp Z _ = NoneE "Too many recursive calls"
>   parseAtomicExp (S steps') xs =
>     (do (_, rest) <- expect "true" xs
>         pure (BTrue, rest))
>     <|>
>     (do (_, rest) <- expect "false" xs
>         pure (BFalse, rest))
>     <|>
>     (do (e, rest) <- firstExpect "not" (parseAtomicExp steps') xs
>         pure (BNot e, rest))
>     <|>
>     (do (e, rest) <- firstExpect "(" (parseConjunctionExp steps') xs
>         (_, rest') <- expect ")" rest
>         pure (e, rest'))
>     <|>
>     (do (e, rest) <- parseProductExp steps' xs
>         ((do (e', rest') <- firstExpect "==" (parseAExp steps') rest
>              pure (BEq e e', rest'))
>          <|>
>          (do (e', rest') <- firstExpect "<=" (parseAExp steps') rest
>              pure (BLe e e', rest'))
>          <|>
>          (NoneE "Expected '==' or '<=' after arithmetic expression")))
>
>   parseConjunctionExp : (steps : Nat) -> Parser BExp
>   parseConjunctionExp Z _ = NoneE "Too many recursive calls"
>   parseConjunctionExp (S steps') xs =
>     do (e, rest) <- parseAtomicExp steps' xs
>        (es, rest') <- many (firstExpect "&&" (parseAtomicExp steps')) steps' rest
>        pure (foldl BAnd e es, rest')
>
> parseBExp : (steps : Nat) -> Parser BExp
> parseBExp = parseConjunctionExp
>
> testParsing : (p : Nat -> Parser t) -> (s : String) -> OptionE (t, List Token)
> testParsing p s = p 100 (tokenize s)
>

\todo[inline]{The second one seems designed to fail}

```idris
λΠ> testParsing parseProductExp "x*y*(x*x)*x"

λΠ> testParsing parseConjunctionExp "not((x==x||x*x<=(x*x)*x)&&x==x"
```

Parsing commands:

> mutual
>   parseSimpleCommand : (steps : Nat) -> Parser Com
>   parseSimpleCommand Z _ = NoneE "Too many recursive calls"
>   parseSimpleCommand (S steps') xs =
>     (do (_, rest) <- expect "SKIP" xs
>         pure (SKIP, rest))
>     <|>
>     (do (e, rest) <- firstExpect "IF" (parseBExp steps') xs
>         (c, rest') <- firstExpect "THEN" (parseSequencedCommand steps') rest
>         (c', rest'') <- firstExpect "ELSE" (parseSequencedCommand steps') rest'
>         (_, rest''') <- expect "END" rest''
>         pure (IFB e THEN c ELSE c' FI, rest'''))
>     <|>
>     (do (e, rest) <- firstExpect "WHILE" (parseBExp steps') xs
>         (c, rest') <- firstExpect "DO" (parseSequencedCommand steps') rest
>         (_, rest'') <- expect "END" rest'
>         pure (WHILE e DO c END, rest''))
>     <|>
>     (do (i, rest) <- parseIdentifier xs;
>         (e, rest') <- firstExpect ":=" (parseAExp steps') rest
>         pure (i ::= e, rest'))
>
>   parseSequencedCommand : (steps : Nat) -> Parser Com
>   parseSequencedCommand Z _ = NoneE "Too many recursive calls"
>   parseSequencedCommand (S steps') xs =
>     do (c, rest) <- parseSimpleCommand steps' xs
>        ((do (c', rest') <- firstExpect ";;" (parseSequencedCommand steps') rest
>             pure (c ;; c', rest'))
>         <|>
>         (pure (c, rest)))
>
> bignumber : Nat
> bignumber = 1000
>
> parse : (str : String) -> OptionE (Com, List Token)
> parse str = parseSequencedCommand bignumber (tokenize str)
>

== Examples

```idris
λΠ> parse "IF x == y + 1 + 2 - y * 6 + 3 THEN x := x * 1;; y := 0 ELSE SKIP END"
SomeE (CIf (BEq (AId (MkId "x")) (APlus (AMinus (APlus (APlus (AId (MkId "y")) (ANum 1)) (ANum 2)) (AMult (AId (MkId "y")) (ANum 6))) (ANum 3)))
           (CSeq (CAss (MkId "x") (AMult (AId (MkId "x")) (ANum 1))) (CAss (MkId "y") (ANum 0)))
           CSkip,
       []) : OptionE (Com, List String)

λΠ> parse "SKIP;; z:=x*y*(x*x);; WHILE x==x DO IF z <= z*z && not x == 2 THEN x := z;; y := z ELSE SKIP END;; SKIP END;; x:=z"
```

\todo[inline]{This one is repeated twice in the book for some reason}

```idris
SomeE (CSeq CSkip
            (CSeq (CAss (MkId "z") (AMult (AMult (AId (MkId "x")) (AId (MkId "y"))) (AMult (AId (MkId "x")) (AId (MkId "x")))))
                  (CSeq (CWhile (BEq (AId (MkId "x")) (AId (MkId "x")))
                                (CSeq (CIf (BAnd (BLe (AId (MkId "z")) (AMult (AId (MkId "z")) (AId (MkId "z")))) (BNot (BEq (AId (MkId "x")) (ANum 2))))
                                           (CSeq (CAss (MkId "x") (AId (MkId "z"))) (CAss (MkId "y") (AId (MkId "z"))))
                                           CSkip)
                                      CSkip))
                        (CAss (MkId "x") (AId (MkId "z"))))),
       []) : OptionE (Com, List String)
```