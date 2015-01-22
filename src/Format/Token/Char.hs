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
import Format.Combinator.Prim (ManyC)
import Format.Token.Base

type SatisfyChar c m = SatisfyC c m Char
type MatchChar c m = MatchC c m Char
type TokensChar c m = TokensC c m Char
type ManyChar c m = ManyToken c m Char

char :: MatchChar c m => Char -> Format c m Char '[]
char = match

-- TODO add spaces

space :: SatisfyChar c m => SFormat c m Char Char
space = satisfy isSpace

newline :: MatchChar c m => Format c m Char '[]
newline = char '\n'

crlf :: (Use Format c m Char '[], 
         Use Seq    c m Char '[],
         MatchChar  c m) => Format c m Char '[]
crlf = char '\r' *> char '\n'

endOfLine :: (Use Seq    c m Char '[],
              Use Alt    c m Char '[], 
              Use Format c m Char '[],
              MatchChar c m          ) => Format c m Char '[]
endOfLine = newline <|> crlf

tab :: MatchChar c m => Format c m Char '[]
tab = char '\t'

upper :: SatisfyChar c m => SFormat c m Char Char
upper = satisfy isUpper

lower :: SatisfyChar c m => SFormat c m Char Char
lower = satisfy isLower

alphaNum :: SatisfyChar c m => SFormat c m Char Char
alphaNum = satisfy isAlphaNum

letter :: SatisfyChar c m => SFormat c m Char Char
letter = satisfy isAlpha

digit :: SatisfyChar c m => SFormat c m Char Char
digit = satisfy isDigit

hexDigit :: SatisfyChar c m => SFormat c m Char Char
hexDigit = satisfy isHexDigit

octDigit :: SatisfyChar c m => SFormat c m Char Char
octDigit = satisfy isOctDigit

string :: TokensChar c m => String -> Format c m Char '[]
string s = tokens s
