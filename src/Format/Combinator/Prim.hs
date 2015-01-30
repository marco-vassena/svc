{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}

-- This module defines basic primitive combinators.
-- Note that like with their applicative counterpart the 
-- underlying semantics must fail eventually in order to terminate.
-- The 'SList' values must be explicitly provided.

module Format.Combinator.Prim where

import Data.HList
import Data.Maybe
import Format.Syntax
import Format.Combinator.Base
import Control.Isomorphism.Partial
import qualified Control.Isomorphism.Partial as C

many :: AlternativeC c m i => SList xs -> Format c m i xs -> Format c m i (Map [] xs)
many s f = some s f
        <|> allEmpty s <$> unit

some :: AlternativeC c m i => SList xs -> Format c m i xs -> Format c m i (Map [] xs)
some s f = combine s <$> f <*> many s f

sepBy :: AlternativeC c m i
      => Format c m i '[] -> SList xs -> Format c m i xs -> Format c m i (Map [] xs)
sepBy sep s f = sepBy1 sep s f 
             <|> allEmpty s <$> unit

sepBy1 :: AlternativeC c m i
       => Format c m i '[] -> SList xs -> Format c m i xs -> Format c m i (Map [] xs)
sepBy1 sep s f = combine s <$> f <*> many s (sep *> f)

-- | The `chainl1` combinator is used to parse a
-- left-associative chain of infix operators. 
chainl1 :: AlternativeC c m i 
        => SFormat c m i a -> SFormat c m i b -> Iso '[a, b, a] '[a] -> SFormat c m i a
chainl1 arg op f = C.foldl s f <$> arg <*> many s (op <*> arg)
  where s = SCons (SCons SNil)

count :: AlternativeC c m i
      => SList xs -> Int -> Format c m i xs -> Format c m i (Map [] xs)
count s n f | n <= 0    = allEmpty s <$> unit 
count s n f | otherwise = combine s  <$> f <*> count s (n - 1) f

manyTill :: AlternativeC c m i
         => Format c m i '[] -> SList xs -> Format c m i xs -> Format c m i (Map [] xs)
manyTill end s p =  combine  s <$> p   <*> manyTill end s p
                <|> allEmpty s <$> end
