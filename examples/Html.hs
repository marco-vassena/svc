-- A format that recognizes html tags
-- The characters '<' '>' '!' '-' are considered for tags only,
-- thus they may not appear with plain text.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Html where

import Data.HList
import Format.Base
import Format.Token
import qualified Format.Token as F
import Format.Token.Char
import Format.Combinator
import Format.Printer
import Format.Printer.Naive
import Format.Parser
import Format.Parser.Naive
import Control.Isomorphism.Partial
import qualified Control.Isomorphism.Partial.Prim as C
import Control.Isomorphism.Partial.Constructors

data Tag =
    Open String [Attribute]
  | Close String
  | CChar Char
  | Comment String
  deriving Show

-- Tag isomorphisms
open :: Iso '[String, [Attribute]] '[Tag]
open = Iso (Just . hsingleton . happly Open) from (SCons (SCons SNil)) (SCons SNil)
  where from :: PFunction '[Tag] '[String, [Attribute]]
        from (Cons (Open s as) _) = Just $ Cons s (Cons as Nil)
        from _           = Nothing

close :: Iso '[String] '[Tag]
close = Iso (Just . hsingleton . happly Close) from (SCons SNil) (SCons SNil)
  where from :: PFunction '[Tag] '[String]
        from (Cons (Close s) _) = Just $ Cons s Nil
        from _                  = Nothing

cChar :: Iso '[Char] '[Tag]
cChar = Iso (Just . hsingleton . happly CChar) from (SCons SNil) (SCons SNil)
  where from :: PFunction '[Tag] '[Char]
        from (Cons (CChar c) _) = Just $ Cons c Nil
        from _                     = Nothing

comment :: Iso '[String] '[Tag]
comment = Iso (Just . hsingleton . happly Comment) from (SCons SNil) (SCons SNil)
  where from :: PFunction '[Tag] '[String]
        from (Cons (Comment s) _) = Just $ Cons s Nil
        from _                    = Nothing

data Attribute = Attr String String
  deriving Show

attr :: Iso '[String, String] '[Attribute]
attr = Iso (Just . hsingleton . happly Attr) from (SCons (SCons SNil)) (SCons SNil)
  where from :: PFunction '[Attribute] '[String, String]
        from (Cons (Attr k v) _) = Just $ Cons k (Cons v Nil)

--------------------------------------------------------------------------------
-- Tag format

name :: SFormat m Char String
name = cons <$> letter <@> rest
  where rest = many (letter <|> digit <|> periodOrHyp)
        periodOrHyp = oneOf ".-"

openTag :: SFormat m Char Tag
openTag = open <$> char '<' @> name <@> (Pure (hsingleton [])) <@ char '>' -- space @> sepBy attribute space)
  where space = char ' '

closeTag :: SFormat m Char Tag
closeTag = close <$> string "</" @> name <@ char '>'

commentTag :: SFormat m Char Tag
commentTag = comment <$> string "<!--" @> F.takeWhile (/= '-') <@ string "-->" -- improve

cCharTag :: SFormat m Char Tag
cCharTag = cChar <$> noneOf "<>!-"

--------------------------------------------------------------------------------
-- Attribute format

attribute :: Format m Char '[Attribute]
attribute = attr <$> name <@> char '=' @> value

value :: SFormat m Char String
value =  char '\'' @> many (noneOf "'") <@ char '\''
     <|> char '"' @> many (noneOf "\"") <@ char '"'

--------------------------------------------------------------------------------

html :: SFormat m Char [Tag]
html = many tag

tag :: SFormat m Char Tag
tag = openTag <|> closeTag <|> commentTag <|> cCharTag

htmlInput :: String
htmlInput = "<html>\n<body>\n\n<h1>My First Heading</h1>\n\n\
             \<p>My first paragraph.</p>\n\n</body>\n</html>"

parseHtml :: Parser Char (HList '[[Tag]])
parseHtml = mkParser html

printHtml :: HList '[[Tag]] -> Maybe String
printHtml = mkPrinter html

main :: IO ()
main = do
  h <- parseM parseHtml htmlInput
  case printHtml h of
    Just s -> putStrLn s
    Nothing -> fail "Printer Failed"
