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
import Data.TypeList.HList
import Format.Syntax
import Format.Combinator
import Format.Token.Base

type FormatC c m = (Use Satisfy c m Char, Use Format c m Char, Use Help c m Char)

-- | @char c@ is a format that expects the character @c@.
char :: MatchC c m Char => Char -> Format c m Char '[]
char c = match c <?> show [c]

-- | Accepts any character.
anyChar :: MatchC c m Char => SFormat c m Char Char
anyChar = token

-- | Expects white-space characeter.
space :: FormatC c m => SFormat c m Char Char
space = satisfy isSpace <?> "space"

-- | Expects a newline character.
newline :: MatchC c m Char => Format c m Char '[]
newline = char '\n' <?> "lf new-line"

-- | A format that exepcts the carriage return character followed by a new line character.
crlf :: (FormatC c m, AlternativeC c m Char) => Format c m Char '[]
crlf = char '\r' *> char '\n' <?> "crlf new-line"

-- | Expects any kind of endOfLine.
endOfLine :: (FormatC c m, AlternativeC c m Char) => Format c m Char '[]
endOfLine = newline <|> crlf <?> "new-line"

-- | Expects a tab character.
tab :: MatchC c m Char => Format c m Char '[]
tab = char '\t' <?> "tab"

-- | Expects an upper case character [A-Z].
upper :: FormatC c m => SFormat c m Char Char
upper = satisfy isUpper <?> "uppercase letter"

-- | Expects a lower case case character [a-z].
lower :: FormatC c m => SFormat c m Char Char
lower = satisfy isLower <?> "lowercase letter"

-- | Expects a letter or a digit.
alphaNum :: FormatC c m => SFormat c m Char Char
alphaNum = satisfy isAlphaNum <?> "letter or digit"

-- | Expects a letter (upper or lower case).
letter :: FormatC c m => SFormat c m Char Char
letter = satisfy isAlpha <?> "letter"

-- | Expects a digit [0-9]
digit :: FormatC c m => SFormat c m Char Char
digit = satisfy isDigit <?> "digit"

-- | Expects an hexadecimal digit.
hexDigit :: FormatC c m => SFormat c m Char Char
hexDigit = satisfy isHexDigit  <?> "hexadecimal digit"

-- | Expects an octal digit.
octDigit :: FormatC c m => SFormat c m Char Char
octDigit = satisfy isOctDigit <?> "octal digit"

-- | Expects the given string.
string :: (MatchC c m Char, AlternativeC c m Char) => String -> Format c m Char '[]
string s = tokens s <?> s

-- A format lexeme for non-negative integers.
integer :: (MatchC c m Char, AlternativeC c m Char) => Format c m Char '[Int]
integer = int <$> some digit
