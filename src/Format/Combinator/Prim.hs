{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

-- This module defines basic combinators.
-- The 'SList' values must be explicitly provided.

module Format.Combinator.Prim where

import Data.HList
import Data.Maybe
import Format.Base
import Format.Combinator.Base
import Control.Isomorphism.Partial
import qualified Control.Isomorphism.Partial as C

many :: SList xs -> Format m i xs -> Format m i (Map [] xs)
many s f = some s f
        <|> inverse (allEmpty s) <$> unit

some :: SList xs -> Format m i xs -> Format m i (Map [] xs)
some s f = inverse (combine s) <$> f <@> many s f

sepBy :: SList xs -> Format m i xs -> Format m i '[] -> Format m i (Map [] xs)
sepBy s f sep = sepBy1 s f sep
             <|> inverse (allEmpty s) <$> unit

sepBy1 :: SList xs -> Format m i xs -> Format m i '[] -> Format m i (Map [] xs)
sepBy1 s f sep = inverse (combine s) <$> f <@> many s (sep @> f)

-- | The `chainl1` combinator is used to parse a
-- left-associative chain of infix operators. 
chainl1 :: SFormat m i a -> SFormat m i b -> Iso '[a, b, a] '[a] -> SFormat m i a
chainl1 arg op f = C.foldl s f <$> arg <@> many s (op <@> arg)
  where s = SCons (SCons SNil)

-- FIX: wrong when xs = '[]
count :: SList xs -> Int -> Format m i xs -> Format m i (Map [] xs)
count s n f | n <= 0    = inverse (allEmpty s) <$> unit 
count s n f | otherwise = inverse (combine s) <$> f <@> count s (n - 1) f
