{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}

module Util where

import Format.Syntax
import Format.Combinator
import Format.Token
import Control.Isomorphism.Partial
import Data.TypeList.HList

-- | A lexeme that recognizes integers.
int :: (FormatC c m, AlternativeC c m Char) => SFormat c m Char Int
int = readShow <$> some digit
  
-- | An isomorphism naturally defined for Read/Show objects.
readShow :: (Read a, Show a) => Iso '[String] '[a] 
readShow = Iso r s p p
  where p = SCons SNil
        r = hsingleton . happly read
        s = Just . hsingleton . happly show
