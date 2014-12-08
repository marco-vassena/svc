-- | Common char-based formats

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Format.Char where

import Data.Char
import Format.Base
import Format.Combinator
import Control.Applicative (pure, (*>))
import qualified Text.Parsec.Char as P

-- TODO anyOf maybe generalized for any a

-- | It represents a set of characters to be matched.
data AnyOf = AnyOf Char [Char]

anyOf :: StreamChar i => [Char] -> Format i '[]
anyOf (c:cs) = Meta (AnyOf c cs)
anyOf [] = error "Format.Char.anyOf : empty list"

spaces :: StreamChar i => Format i '[]
spaces = (many spaceChars) @> unit
  where spaceChars = anyOf " \t\n\r\f\v\xa0"

space :: StreamChar i => SFormat i Char
space = satisfy isSpace char

newline :: StreamChar i => Format i '[]
newline = tag '\n'

crlf :: StreamChar i => Format i '[]
crlf = tag "\r\n"

endOfLine :: StreamChar i => Format i '[]
endOfLine = newline <|> crlf

tab :: StreamChar i => Format i '[]
tab = tag '\t'

upper :: StreamChar i => SFormat i Char
upper = satisfy isUpper char

lower :: StreamChar i => SFormat i Char
lower = satisfy isLower char

alphaNum :: StreamChar i => SFormat i Char
alphaNum = satisfy isAlphaNum char

letter :: StreamChar i => SFormat i Char
letter = satisfy isAlpha char

digit :: StreamChar i => SFormat i Char
digit = satisfy isDigit char

hexDigit :: StreamChar i => SFormat i Char
hexDigit = satisfy isHexDigit char

octDigit :: StreamChar i => SFormat i Char
octDigit = satisfy isOctDigit char

--------------------------------------------------------------------------------
instance StringLike i => Printable i AnyOf where
  printer (AnyOf c cs) = pure $ singleton c

instance StreamChar i => Match i AnyOf where
  match a@(AnyOf c cs) = P.oneOf (c:cs) *> pure a
