{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}

-- This module defines basic primitive combinators.
-- Note that repetition combinators such as @many@ and @some@
-- won't terminate if the repeated action never fails.
-- This behaviour is consistent with their applicative counterpart.
-- underlying semantics must fail eventually in order to terminate.
-- The 'SList' values must be explicitly provided.

module Format.Combinator.Prim where

import Data.TypeList.HList
import Data.Maybe
import Format.Syntax
import Format.Combinator.Base
import Control.Isomorphism.Partial
import qualified Control.Isomorphism.Partial as C

-- Zero or more.
many :: AlternativeC c m i => SList xs -> Format c m i xs -> Format c m i (Map [] xs)
many s f = some s f
        <|> allEmpty s <$> unit

-- One or more.
some :: AlternativeC c m i => SList xs -> Format c m i xs -> Format c m i (Map [] xs)
some s f = combine s <$> f <*> many s f

-- @sepBy sep s f@ is a format composed by zero or more occurences of @f@ separated by @sep@.
sepBy :: AlternativeC c m i
      => Format c m i '[] -> SList xs -> Format c m i xs -> Format c m i (Map [] xs)
sepBy sep s f = sepBy1 sep s f 
             <|> allEmpty s <$> unit

-- @sepBy1 sep s f@ is a format composed by one or more occurences of @f@ separated by @sep@.
sepBy1 :: AlternativeC c m i
       => Format c m i '[] -> SList xs -> Format c m i xs -> Format c m i (Map [] xs)
sepBy1 sep s f = combine s <$> f <*> many s (sep *> f)

-- | The `chainl1` combinator is used to parse a
-- left-associative chain of infix operators. 
chainl1 :: AlternativeC c m i 
        => SFormat c m i a -> SFormat c m i b -> Iso '[a, b, a] '[a] -> SFormat c m i a
chainl1 arg op f = C.foldl s f <$> arg <*> many s (op <*> arg)
  where s = SCons (SCons SNil)

-- | The `chainr1` combinator is used to parse a
-- right-associative chain of infix operators. 
chainr1 :: AlternativeC c m i 
        => SFormat c m i a -> SFormat c m i b -> Iso '[a, b, a] '[a] -> SFormat c m i a
chainr1 arg op f = C.foldr s f <$> (commute s (SCons SNil) <$> (many s (arg <*> op) <*> arg))
  where s = SCons (SCons SNil)

-- @count s n f@ repeats @n@ times the format @f@.
count :: AlternativeC c m i
      => SList xs -> Int -> Format c m i xs -> Format c m i (Map [] xs)
count s n f | n <= 0    = allEmpty s <$> unit 
count s n f | otherwise = combine s  <$> f <*> count s (n - 1) f

-- @manyTill f end@ repeats the format @f@ until the format @end@ is matched.
manyTill :: AlternativeC c m i
         => Format c m i '[] -> SList xs -> Format c m i xs -> Format c m i (Map [] xs)
manyTill end s p =  combine  s <$> p   <*> manyTill end s p
                <|> allEmpty s <$> end
