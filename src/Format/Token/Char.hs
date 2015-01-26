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
import Format.Syntax
import Format.Combinator
import Format.Combinator.Prim
import Format.Token.Base

type FormatC c m = (Use Satisfy c m Char, Use Format c m Char, Use Help c m Char)

char :: MatchC c m Char => Char -> Format c m Char '[]
char c = match c <?> show [c]

anyChar :: Use Satisfy c m Char => SFormat c m Char Char
anyChar = token

-- TODO add spaces

space :: FormatC c m => SFormat c m Char Char
space = satisfy isSpace <?> "space"

newline :: MatchC c m Char => Format c m Char '[]
newline = char '\n' <?> "lf new-line"

crlf :: (FormatC c m, AlternativeC c m Char) => Format c m Char '[]
crlf = char '\r' *> char '\n' <?> "crlf new-line"

endOfLine :: (FormatC c m, AlternativeC c m Char) => Format c m Char '[]
endOfLine = newline <|> crlf <?> "new-line"

tab :: MatchC c m Char => Format c m Char '[]
tab = char '\t' <?> "tab"

upper :: FormatC c m => SFormat c m Char Char
upper = satisfy isUpper <?> "uppercase letter"

lower :: FormatC c m => SFormat c m Char Char
lower = satisfy isLower <?> "lowercase letter"

alphaNum :: FormatC c m => SFormat c m Char Char
alphaNum = satisfy isAlphaNum <?> "letter or digit"

letter :: FormatC c m => SFormat c m Char Char
letter = satisfy isAlpha <?> "letter"

digit :: FormatC c m => SFormat c m Char Char
digit = satisfy isDigit <?> "digit"

hexDigit :: FormatC c m => SFormat c m Char Char
hexDigit = satisfy isHexDigit  <?> "hexadecimal digit"

octDigit :: FormatC c m => SFormat c m Char Char
octDigit = satisfy isOctDigit <?> "octal digit"

string :: (MatchC c m Char, AlternativeC c m Char) => String -> Format c m Char '[]
string s = tokens s
