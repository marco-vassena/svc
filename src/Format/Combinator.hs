{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}

-- This module provides common combinators

module Format.Combinator (
    module Format.Combinator.Base
  , many
  , some
  , sepBy
  , sepBy1
  , count
  , manyTill
  , P.chainl1
  ) where

import Format.Combinator.Base
import qualified Format.Combinator.Prim as P
import Data.HList
import Format.Base

-- TODO remove the KnownSList constraint
many :: (AlternativeC c m i, KnownSList xs) 
     => Format c m i xs -> Format c m i (Map [] xs)
many f = case toSList f of 
          SNil -> P.many0 f
          (SCons s) -> P.many (SCons s) f

-- TODO remove the KnownSList constraint
some :: (AlternativeC c m i, KnownSList xs) 
     => Format c m i xs -> Format c m i (Map [] xs)
some f = case toSList f of 
          SNil -> P.some0 f
          (SCons s) -> P.some (SCons s) f

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
