-- | Common char-based combinators

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module Format.Token.Char where

import Control.Isomorphism.Partial
import Data.Char
import Data.HList
import Format.Base
import Format.Combinator
import Format.Combinator.Prim
import Format.Token.Base

char :: MatchC c m Char => Char -> Format c m Char '[]
char = match

anyChar :: Use Satisfy c m Char => SFormat c m Char Char
anyChar = token

-- TODO add spaces

space :: Use Satisfy c m Char => SFormat c m Char Char
space = satisfy isSpace

newline :: MatchC c m Char => Format c m Char '[]
newline = char '\n'

crlf :: (Use Satisfy c m Char, AlternativeC c m Char) => Format c m Char '[]
crlf = char '\r' *> char '\n'

endOfLine :: (Use Satisfy c m Char, AlternativeC c m Char) => Format c m Char '[]
endOfLine = newline <|> crlf

tab :: MatchC c m Char => Format c m Char '[]
tab = char '\t'

upper :: Use Satisfy c m Char => SFormat c m Char Char
upper = satisfy isUpper

lower :: Use Satisfy c m Char => SFormat c m Char Char
lower = satisfy isLower

alphaNum :: Use Satisfy c m Char => SFormat c m Char Char
alphaNum = satisfy isAlphaNum

letter :: Use Satisfy c m Char => SFormat c m Char Char
letter = satisfy isAlpha

digit :: Use Satisfy c m Char => SFormat c m Char Char
digit = satisfy isDigit

hexDigit :: Use Satisfy c m Char => SFormat c m Char Char
hexDigit = satisfy isHexDigit

octDigit :: Use Satisfy c m Char => SFormat c m Char Char
octDigit = satisfy isOctDigit

string :: (Use Satisfy c m Char, AlternativeC c m Char) => String -> Format c m Char '[]
string s = tokens s
