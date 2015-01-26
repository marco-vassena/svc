{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}

-- This module defines basic combinators.
-- The 'SList' values must be explicitly provided.

module Format.Combinator.Prim where

import Data.HList
import Data.Maybe
import Format.Base
import Format.Combinator.Base
import Control.Isomorphism.Partial
import qualified Control.Isomorphism.Partial as C

many :: AlternativeC c m i => SList xs -> Format c m i xs -> Format c m i (Map [] xs)
many s f = some s f
        <|> inverse (allEmpty s) <$> unit

some :: AlternativeC c m i => SList xs -> Format c m i xs -> Format c m i (Map [] xs)
some s f = inverse (combine s) <$> f <*> many s f

sepBy :: AlternativeC c m i 
      => SList xs -> Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
sepBy s f sep = sepBy1 s f sep
             <|> inverse (allEmpty s) <$> unit

sepBy1 :: AlternativeC c m i 
       => SList xs -> Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
sepBy1 s f sep = inverse (combine s) <$> f <*> many s (sep *> f)

-- | The `chainl1` combinator is used to parse a
-- left-associative chain of infix operators. 
chainl1 :: AlternativeC c m i 
        => SFormat c m i a -> SFormat c m i b -> Iso '[a, b, a] '[a] -> SFormat c m i a
chainl1 arg op f = C.foldl s f <$> arg <*> many s (op <*> arg)
  where s = SCons (SCons SNil)

count :: AlternativeC c m i
      => SList xs -> Int -> Format c m i xs -> Format c m i (Map [] xs)
count s n f | n <= 0    = inverse (allEmpty s) <$> unit 
count s n f | otherwise = inverse (combine s)  <$> f <*> count s (n - 1) f

manyTill :: AlternativeC c m i 
         => SList xs -> Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
manyTill s p end =  inverse (combine  s) <$> p   <*> manyTill s p end
                <|> inverse (allEmpty s) <$> end
