-- Simple, minimal HTML format.

-- Featurs

{-# LANGUAGE DataKinds #-}

module Html where

import Data.HList
import Format.Base
import Format.Token
import Format.Token.Char
import Format.Combinator
import Control.Isomorphism.Partial.Constructors

name :: Format m Char '[ String ]
name = cons <$> letter <@> rest
  where rest = many (letter <|> digit <|> periodOrHyp)
        periodOrHyp = oneOf ".-"

startTag :: Format m Char '[String, [String], [String]]
startTag = char '<' @> (name <@> space @> sepBy attribute space) <@ char '>'
  where space = char ' '

endTag :: Format m Char '[String]
endTag = string "<\\" @> name <@ char '>'

attribute :: Format m Char '[String, String]
attribute = name <@> char '=' @> value

value :: Format m Char '[String]
value =  char '\'' @> many (noneOf "'") <@ char '\''
     <|> char '"' @> many (noneOf "\"") <@ char '"'


