{-# LANGUAGE DataKinds #-}

-- This module defines basic combinators.
-- The 'SList' values must be explicitly provided.

module Format.Combinator.Prim where

import Data.HList
import Format.Base
import Format.Combinator.Base
import Control.Isomorphism.Partial
import qualified Control.Isomorphism.Partial as C


-- The order is relevant: whne printing the second alternative is not productive.
many :: SList xs -> Format m i xs -> Format m i (Map [] xs)
many s f = manyEmpty <$> Pure (hsingleton []) <|> combine s <$> f <@> many s f
  where manyEmpty = Iso from to (SCons SNil) (smap proxyList s)
        from      = Just . happly (unList s)
        to        = Just . hsingleton . toList s

some :: SList xs -> Format m i xs -> Format m i (Map [] xs)
some s f = combine s <$> f <@> many s f


combine s = inverse $ unpack (mapPreservesLength proxyList s) (zipper s)

-- | The `chainl1` combinator is used to parse a
-- left-associative chain of infix operators. 
chainl1 :: SFormat m i a -> SFormat m i b -> Iso '[a, b, a] '[a] -> SFormat m i a
chainl1 arg op f = C.foldl s f <$> arg <@> many s (op <@> arg)
  where s = SCons (SCons SNil)


