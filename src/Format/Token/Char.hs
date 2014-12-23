-- | Common char-based combinators

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Format.Token.Char where

import Data.Char
import Format.Base
import Format.Combinator
import Format.Token.Base

char :: Char -> Format m Char '[]
char = match

-- TODO add spaces

space :: SFormat m Char Char
space = satisfy isSpace

newline :: Format m Char '[]
newline = char '\n'

crlf :: Format m Char '[]
crlf = char '\r' @> char '\n'

endOfLine :: Format m Char '[]
endOfLine = newline <|> crlf

tab :: Format m Char '[]
tab = char '\t'

upper :: SFormat m Char Char
upper = satisfy isUpper

lower :: SFormat m Char Char
lower = satisfy isLower

alphaNum :: SFormat m Char Char
alphaNum = satisfy isAlphaNum

letter :: SFormat m Char Char
letter = satisfy isAlpha

digit :: SFormat m Char Char
digit = satisfy isDigit

hexDigit :: SFormat m Char Char
hexDigit = satisfy isHexDigit

octDigit :: SFormat m Char Char
octDigit = satisfy isOctDigit
