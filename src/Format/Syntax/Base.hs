{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

module Format.Syntax.Base (
    Reify(..)
  , Format(..)
  , format
  , Use(..)
  , SFormat ) where

import Prelude ((.), Bool(..), const, String)
import Data.TypeList.HList
import Data.Type.Equality
import GHC.Exts

-- This is just a wrapper used to unify signatures.
-- It does not "close" the universe.
data Format c (m :: * -> *) (i :: *) (xs :: [*]) where
  Format :: (Reify (a m i), c m i a) => a m i xs -> Format c m i xs

type Use a c m i = c m i (a c)

format :: (Use a c m i, Reify (a c m i)) => a c m i xs -> Format c m i xs
format = Format

-- | 'SFormat' stands for Single Format and represents a 'Format'
-- containing only one target type.
type SFormat c m i a = Format c m i '[ a ]

instance Reify (Format c m i) where
  toSList (Format f) = toSList f
