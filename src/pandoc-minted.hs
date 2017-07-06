#! /usr/bin/env runghc


-- Project-specific Haskell port of Nick Ulle's pandoc-minted.py:
-- https://github.com/nick-ulle/pandoc-minted


import           Data.List           (intercalate)
import           Text.Pandoc.Generic (topDown)
import           Text.Pandoc.JSON


data Minted = MintedInline (String, String) String
            | MintedBlock (String, String) String


instance Show Minted where
  show (MintedInline (attrs, language) contents) =
    "\\mintinline[" ++ attrs ++ "]{" ++ language ++ "}{" ++ contents ++ "}"
  show (MintedBlock (attrs, language) contents) =
    unlines [ "\\begin{minted}[" ++ attrs ++ "]{" ++ language ++ "}"
            , contents
            , "\\end{minted}"
            ]


main :: IO ()
main = toJSONFilter minted


minted :: Pandoc -> Pandoc
minted = topDown (concatMap mintinline) .
         topDown (concatMap mintedBlock)


mintinline :: Inline -> [Inline]
mintinline (Code attr contents) =
  let
    latex = show $ MintedInline (unpackCode attr "text") contents
  in
    [ RawInline (Format "latex") latex ]
mintinline x = [x]


mintedBlock :: Block -> [Block]
mintedBlock (CodeBlock attr contents) =
  let
    latex = show $ MintedBlock (unpackCode attr "text") contents
  in
    [ RawBlock (Format "latex") latex ]
mintedBlock x = [x]


unpackCode :: Attr -> String -> (String, String)
unpackCode (_, [], kvs) defaultLanguage =
  (unpackAttrs kvs, defaultLanguage)
unpackCode (identifier, "sourceCode" : _, kvs) defaultLanguage =
  unpackCode (identifier, ["idris"], kvs) defaultLanguage
unpackCode (_, language : _, kvs) _ =
  (unpackAttrs kvs, language)


unpackAttrs :: [(String, String)] -> String
unpackAttrs kvs = intercalate ", " [ k ++ "=" ++ v  | (k, v) <- kvs ]
