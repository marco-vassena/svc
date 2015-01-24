{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}

-- Char based combinator

module Text.Syntax.Token.Char where

import Data.Char
import Data.HList
import Control.Isomorphism.Partial 
import Text.Syntax.Classes

satisfy :: Syntax f i => (i -> Bool) -> f i '[ i ]
satisfy p = subset (SCons SNil) (happly p) <$> token

digit :: Syntax f Char => f Char '[ Char ]
digit = satisfy isDigit

char :: (Eq i, Syntax f i) => i -> f i '[]
char c = element c <$> token

newline :: Syntax f Char => f Char '[]
newline = char '\n'
