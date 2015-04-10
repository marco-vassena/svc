{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

-- This module provides common combinators.
--
-- Note:
-- A trivial format is of the form Format m i '[].
-- Careless application of mutually recursive combinators such 
-- as many and some with trivial formats may fail to terminate.
-- This happens when the underlying semantics m does not
-- eventually fail. When m is a parser this is not a problem 
-- (the input is always finite), but when m is a printer it does
-- because printing a single character repeatedly never fails.
-- In order to provide a reasonable inverse behaviour these 
-- combinators have the following semantics:
--  * Apply the format as many times as possible (e.g. when parsing)
--  * Unapply the format as few times as possible (e.g. when printing)
-- For instance the format 'many (char ' ')' will match an arbitrary long
-- string of spaces, and when printed will result in the empty string
-- (the shortest string that would succeed when parsing).
-- Similarly 'some (char ' ')' will match a string composed by
-- at least one space and when printing will produce the string " ".
-- ("" would not be recognized by the corresponding parser).

module Format.Combinator (
    module Format.Combinator.Base
  , many
  , some
  , sepBy
  , sepBy1
  , count
  , manyTill
  , P.chainl1
  , P.chainr1
  ) where

import Format.Combinator.Base
import qualified Format.Combinator.Prim as P
import Control.Isomorphism.Partial
import Data.HList
import Format.Syntax

-- '@atMost@ n f k' has the following behaviour:
-- * applies 'f' via 'k' as many times as possible
-- * unapplies 'f' via 'k' at most 'n' times
atMost :: AlternativeC c m i => Int -> Format c m i '[] -> 
          (forall xs . SList xs -> Format c m i xs -> Format c m i (Map [] xs)) -> Format c m i '[]
atMost n f k = ignore hs <$> (k (SCons SNil) (f *> pure hs))
  where hs :: HList '[[a]]
        hs = hsingleton $ replicate n undefined

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
    SNil -> atMost 0 f (P.sepBy sep)
    s -> P.sepBy sep s f

sepBy1 :: (AlternativeC c m i, KnownSList xs) 
       => Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
sepBy1 f sep = 
  case toSList f of 
    SNil -> atMost 1 f (P.sepBy1 sep)
    s -> P.sepBy1 sep s f

count :: (AlternativeC c m i, KnownSList xs) 
      => Int -> Format c m i xs -> Format c m i (Map [] xs)
count = P.count slist

manyTill :: (AlternativeC c m i, KnownSList xs) 
         => Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
manyTill f end = 
  case toSList f of 
    SNil -> atMost 0 f (P.manyTill end)
    s    -> P.manyTill end s f
