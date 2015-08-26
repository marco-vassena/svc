{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}

-- | Definition of the backtracking format combinator and its smart constructor.

module Format.Syntax.Try where

import Data.TypeList.HList
import Format.Syntax.Base

data Try c m i xs where
  Try :: (Reify (a m i), c m i a) => a m i xs -> Try c m i xs

-- Explicit backtracking annotation, used by some parsing libraries such as 
-- Parsec.
try :: (Use Format c m i, Use Try c m i) => Format c m i xs -> Format c m i xs
try = format . Try

instance Reify (Try c m i) where
  toSList (Try f) = toSList f
