{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}

module Format.Syntax.Try where

import Data.TypeList.HList
import Format.Syntax.Base

-- | This piece of format syntax is inspired by the Parsec combinator of the same.
-- It stands for an explicit backtracking annotation.
data Try c m i xs where
  Try :: (Reify (a m i), c m i a) => a m i xs -> Try c m i xs

try :: (Use Try c m i,  
        Use a   c m i,
        Reify (a c m i)) 
      => a c m i xs -> Format c m i xs
try = format . Try

instance Reify (Try c m i) where
  toSList (Try f) = toSList f
