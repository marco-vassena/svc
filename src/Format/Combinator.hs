{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

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
import Control.Isomorphism.Partial
import Data.HList
import Format.Base

-- '@atMost@ n f k' has the following behaviour:
-- * applies 'f' via 'k' as many times as possible
-- * unapplies 'f' via 'k' at most 'n' times
-- This function is usually used with combinators such as 'many' and 'some',
-- which have a total semantics when parsing (longest-match rule), but fail to 
-- terminate when printing. The reason is that a trivial format will never fail 
-- when printed, therefore careless application of many to trivial formats 
-- would result in a loop. This function takes care of that ensuring termination.
atMost :: AlternativeC c m i => Int -> Format c m i '[] -> 
          (forall xs . SList xs -> Format c m i xs -> Format c m i (Map [] xs)) -> Format c m i '[]
atMost n f k = ignore hs <$> (k (SCons SNil) (f *> pure hs))
  where hs :: HList '[[[a]]]
        hs = hsingleton $ replicate n []

many :: AlternativeC c m i
     => Format c m i xs -> Format c m i (Map [] xs)
many f = 
  case toSList f of 
    SNil -> atMost 0 f P.many
    s -> P.many s f

some :: AlternativeC c m i
     => Format c m i xs -> Format c m i (Map [] xs)
some f = 
  case toSList f of 
    SNil -> atMost 1 f P.many
    s -> P.some s f

sepBy :: (AlternativeC c m i, KnownSList xs) 
      => Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
sepBy f sep = 
  case toSList f of 
    SNil -> atMost 0 f (\s f' -> P.sepBy s f' sep)
    s -> P.sepBy s f sep

sepBy1 :: (AlternativeC c m i, KnownSList xs) 
       => Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
sepBy1 f sep = 
  case toSList f of 
    SNil -> atMost 1 f (\s f' -> P.sepBy1 s f' sep)
    s -> P.sepBy1 s f sep

count :: (AlternativeC c m i, KnownSList xs) 
      => Int -> Format c m i xs -> Format c m i (Map [] xs)
count = P.count slist

manyTill :: (AlternativeC c m i, KnownSList xs) 
         => Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
manyTill f end = 
  case toSList f of 
    SNil -> atMost 0 f (\s f' -> P.manyTill s f' end)
    s    -> P.manyTill s f end
