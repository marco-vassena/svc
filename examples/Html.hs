-- A format that recognizes html tags
-- The characters '<' '>' '!' '-' are considered for tags only,
-- thus they may not appear with plain text.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Html where

import Data.HList
import Data.ByteString hiding (cons, putStrLn)
import Format.Base
import Format.Token
import qualified Format.Token as F
import Format.Token.Char
import Format.Combinator
import Format.Printer
import Format.Printer.Naive
import Format.Parser
import Format.Parser.Attoparsec
import Format.Parser.Generic
import Control.Applicative ((<*))
import Control.Isomorphism.Partial
import qualified Control.Isomorphism.Partial.Prim as C
import Control.Isomorphism.Partial.Constructors

import Data.Attoparsec.ByteString.Char8 (Parser, parseOnly, endOfInput)

data Tag =
    Open String [Attribute]
  | Close String
--  | CChar Char
  | Content String
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

--cChar :: Iso '[Char] '[Tag]
--cChar = Iso (Just . hsingleton . happly CChar) from (SCons SNil) (SCons SNil)
--  where from :: PFunction '[Tag] '[Char]
--        from (Cons (CChar c) _) = Just $ Cons c Nil
--        from _                     = Nothing

content :: Iso '[String] '[Tag]
content = Iso (Just . hsingleton . happly Content) from (SCons SNil) (SCons SNil)
  where from :: PFunction '[Tag] '[String]
        from (Cons (Content s) _) = Just $ Cons s Nil

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
commentTag = comment <$> string "<!--" @> manyTill token (string "-->")

--cCharTag :: SFormat m Char Tag
--cCharTag = cChar <$> noneOf "<>!-"

contentTag :: SFormat m Char Tag
contentTag = content <$> some (satisfy (/= '<'))

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
tag = openTag <|> closeTag <|> commentTag <|> contentTag

htmlInput :: ByteString
htmlInput = "<html>\n<body>\n\n<h1>My First Heading</h1>\n\n\
             \<p>My first paragraph.</p>\n\n</body>\n</html>"

parseHtml :: Parser (HList '[[Tag]])
parseHtml = mkParser html

printHtml :: HList '[[Tag]] -> Maybe String
printHtml = mkPrinter html

main :: IO ()
main = do
  case parseOnly (parseHtml <* endOfInput) htmlInput of
    Left err -> fail err
    Right h -> 
      case printHtml h of
        Just s -> putStrLn s
        Nothing -> fail "Printer Failed"
