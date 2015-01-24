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
  ) where

import Format.Combinator.Base
import qualified Format.Combinator.Prim as P
import Data.HList
import Format.Base

many :: (AlternativeC c m i, KnownSList xs) 
     => Format c m i xs -> Format c m i (Map [] xs)
many = P.many slist

some :: (AlternativeC c m i, KnownSList xs) 
     => Format c m i xs -> Format c m i (Map [] xs)
some = P.some slist

sepBy :: (AlternativeC c m i, KnownSList xs) 
      => Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
sepBy = P.sepBy slist

sepBy1 :: (AlternativeC c m i, KnownSList xs) 
       => Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
sepBy1 = P.sepBy1 slist

count :: (AlternativeC c m i, KnownSList xs) 
      => Int -> Format c m i xs -> Format c m i (Map [] xs)
count = P.count slist

manyTill :: (AlternativeC c m i, KnownSList xs) 
         => Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
manyTill = P.manyTill slist
