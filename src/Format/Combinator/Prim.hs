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

type ManyC c m i xs = (Use Alt c m i (Map [] xs),
                       Use Format c m i (Map [] xs),
                       Use FMap c m i (Map [] xs),
                       Use Format c m i '[], 
                       Use Pure c m i '[],
                       Use Format c m i (Append xs (Map [] xs)),
                       Use Format c m i xs,
                       Use Seq c m i (Append xs (Map [] xs)))

type SepByC c m i xs = (ManyC c m i xs, Use Seq c m i xs)

type ChainC c m i a b = (Use Format c m i '[b], 
                         Use Format c m i '[a],
                         Use Format c m i '[[b], [a]],
                         Use Format c m i '[a, [b], [a]],
                         Use Seq c m i '[a, [b], [a]],
                         Use Seq c m i '[b, a],
                         Use FMap c m i '[a],
                         Use Alt c m i '[[b], [a]],
                         Use FMap c m i '[[b], [a]],
                         Use Format c m i '[],
                         Use Pure c m i '[],
                         Use Format c m i '[b, a, [b], [a]],
                         Use Format c m i '[b, a],
                         Use Seq c m i '[b, a, [b], [a]])

many :: ManyC c m i xs => SList xs -> Format c m i xs -> Format c m i (Map [] xs)
many s f = some s f
        <|> inverse (allEmpty s) <$> unit

some :: ManyC c m i xs => SList xs -> Format c m i xs -> Format c m i (Map [] xs)
some s f = inverse (combine s) <$> f <*> many s f

sepBy :: SepByC c m i xs => SList xs -> Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
sepBy s f sep = sepBy1 s f sep
             <|> inverse (allEmpty s) <$> unit

sepBy1 :: SepByC c m i xs => SList xs -> Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
sepBy1 s f sep = inverse (combine s) <$> f <*> many s (sep *> f)

-- | The `chainl1` combinator is used to parse a
-- left-associative chain of infix operators. 
chainl1 :: ChainC c m i a b => SFormat c m i a -> SFormat c m i b -> Iso '[a, b, a] '[a] -> SFormat c m i a
chainl1 arg op f = C.foldl s f <$> arg <*> many s (op <*> arg)
  where s = SCons (SCons SNil)

count :: ManyC c m i xs => SList xs -> Int -> Format c m i xs -> Format c m i (Map [] xs)
count s n f | n <= 0    = inverse (allEmpty s) <$> unit 
count s n f | otherwise = inverse (combine s) <$> f <*> count s (n - 1) f

manyTill :: ManyC c m i xs => SList xs -> Format c m i xs -> Format c m i '[] -> Format c m i (Map [] xs)
manyTill s p end =  inverse (combine  s) <$> p   <*> manyTill s p end
                <|> inverse (allEmpty s) <$> end
