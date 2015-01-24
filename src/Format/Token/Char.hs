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

type MatchChar c m = (ApplicativeC c m Char, Use Token c m Char)

char :: MatchChar c m => Char -> Format c m Char '[]
char = match

-- TODO add spaces

space :: Use Satisfy c m Char => SFormat c m Char Char
space = satisfy isSpace

newline :: MatchChar c m => Format c m Char '[]
newline = char '\n'

crlf :: MatchChar  c m => Format c m Char '[]
crlf = char '\r' *> char '\n'

endOfLine :: (MatchChar c m, Use Alt c m Char) => Format c m Char '[]
endOfLine = newline <|> crlf

tab :: MatchChar c m => Format c m Char '[]
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

string :: MatchChar c m => String -> Format c m Char '[]
string s = tokens s
