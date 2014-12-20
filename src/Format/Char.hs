-- | Common token-based formats

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

spaces :: Format m Char '[]
spaces = (many spaceChars) @> unit
  where spaceChars = anyOf " \t\n\r\f\v\xa0"

space :: SFormat m Char Char
space = satisfy isSpace token

newline :: Format m Char '[]
newline = match '\n'

crlf :: Format m Char '[]
crlf = match "\r\n"

endOfLine :: Format m Char '[]
endOfLine = newline <|> crlf

tab :: Format m Char '[]
tab = match '\t'

upper :: SFormat m Char Char
upper = satisfy isUpper token

lower :: SFormat m Char Char
lower = satisfy isLower token

alphaNum :: SFormat m Char Char
alphaNum = satisfy isAlphaNum token

letter :: SFormat m Char Char
letter = satisfy isAlpha token

digit :: SFormat m Char Char
digit = satisfy isDigit token

hexDigit :: SFormat m Char Char
hexDigit = satisfy isHexDigit token

octDigit :: SFormat m Char Char
octDigit = satisfy isOctDigit token
