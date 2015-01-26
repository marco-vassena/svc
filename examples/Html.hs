-- A format that recognizes html tags
-- The characters '<' '>' '!' '-' are considered for tags only,
-- thus they may not appear with plain text.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}

module Html where

import Data.HList
import Format.Syntax hiding (fail)
import Format.Token
import qualified Format.Token as F
import Format.Token.Char
import Format.Combinator
import Format.Printer
import Format.Printer.Naive
import Format.Parser
import Format.Parser.Parsec
import Format.Parser.GParser
import qualified Control.Applicative as A
import Control.Isomorphism.Partial
import qualified Control.Isomorphism.Partial.Prim as C
import Control.Isomorphism.Partial.Constructors

import Text.Parsec (Parsec, eof, parse)

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

name :: (AlternativeC c m Char, Use Satisfy c m Char) 
        => SFormat c m Char String
name = cons <$> letter <*> rest
  where rest = many (letter <|> digit <|> periodOrHyp)
        periodOrHyp = oneOf ".-"

openTag :: (AlternativeC c m Char, Use Satisfy c m Char) 
         => SFormat c m Char Tag
openTag = open <$> char '<' *> name <*> (Pure (hsingleton [])) <* char '>' -- space *> sepBy attribute space)

closeTag :: (AlternativeC c m Char, Use Satisfy c m Char) 
         => SFormat c m Char Tag
closeTag = close <$> string "</" *> name <* char '>'

commentTag :: (AlternativeC c m Char, Use Satisfy c m Char) 
           => SFormat c m Char Tag
commentTag = comment <$> string "<!--" *> manyTill token (string "-->")

--cCharTag :: SFormat c m Char Tag
--cCharTag = cChar <$> noneOf "<>!-"

contentTag :: (AlternativeC c m Char, Use Satisfy c m Char) 
           => SFormat c m Char Tag
contentTag = content <$> some (satisfy (/= '<'))

--------------------------------------------------------------------------------
-- Attribute format

attribute :: (AlternativeC c m Char, Use Satisfy c m Char) 
          => Format c m Char '[Attribute]
attribute = attr <$> name <*> (char '=' *> value)

value :: (AlternativeC c m Char, Use Satisfy c m Char)
      => SFormat c m Char String
value =  char '\'' *> many (noneOf "'") <* char '\''
     <|> char '"' *> many (noneOf "\"") <* char '"'

--------------------------------------------------------------------------------

html :: (AlternativeC c m Char, Use Satisfy c m Char)
     => SFormat c m Char [Tag]
html = many tag

-- Here we should use try because openTag and closeTag overlap 
tag :: (AlternativeC c m Char, Use Satisfy c m Char)
    =>  SFormat c m Char Tag
tag = openTag <|> closeTag <|> commentTag <|> contentTag  

htmlInput :: String
htmlInput = "<html>\n<body>\n\n<h1>My First Heading</h1>\n\n\
             \<p>My first paragraph.</p>\n\n</body>\n</html>"

parseHtml :: Parsec String () [Tag]
parseHtml = hHead A.<$> mkParser html A.<* eof

printHtml :: [Tag] -> Maybe String
printHtml = mkPrinter html . hsingleton

main :: IO ()
main = do
  case parse parseHtml "" htmlInput of
    Left err -> fail (show err)
    Right h -> 
      case printHtml h of
        Just s -> putStrLn s
        Nothing -> fail "Printer Failed"
