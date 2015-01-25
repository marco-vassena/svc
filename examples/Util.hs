{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}

module Util where

import Format.Base
import Format.Combinator
import Format.Token
import Control.Isomorphism.Partial
import Data.HList

-- | A lexeme that recognizes integers.
int :: (Use Satisfy c m Char, AlternativeC c m Char) => SFormat c m Char Int
int = readShow <$> some digit
  
-- | An isomorphism naturally defined for Read/Show objects.
readShow :: (Read a, Show a) => Iso '[String] '[a] 
readShow = Iso r s p p
  where p = SCons SNil
        r = Just . hsingleton . happly read
        s = Just . hsingleton . happly show
