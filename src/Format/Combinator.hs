{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}

-- This module provides common combinators

module Format.Combinator (
    module Format.Combinator.Base
  , many
  , some
  , sepBy
  , sepBy1
  , count
  , manyTill
  , ManyC
  , SepByC
  ) where

import Format.Combinator.Base
import Format.Combinator.Prim (ManyC, SepByC)
import qualified Format.Combinator.Prim as P
import Data.HList
import Format.Base

many :: (ManyC c m i xs, KnownSList xs) => Format c m i xs -> Format c m i (Map [] xs)
many = P.many slist

some :: (ManyC c m i xs, KnownSList xs) => Format c m i xs -> Format c m i (Map [] xs)
some = P.some slist

sepBy :: (SepByC c m i xs, KnownSList xs) => Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
sepBy = P.sepBy slist

sepBy1 :: (SepByC c m i xs, KnownSList xs) => Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
sepBy1 = P.sepBy1 slist

count :: (ManyC c m i xs, KnownSList xs) => Int -> Format c m i xs -> Format c m i (Map [] xs)
count = P.count slist

manyTill :: (ManyC c m i xs, KnownSList xs) => Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
manyTill = P.manyTill slist
