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
many s f = inverse (combine s) <$> f <@> many s f
        <|> manyEmpty s <$> Pure (hsingleton [])

manyEmpty :: SList xs -> Iso '[ [ HList xs ] ] (Map [] xs)
manyEmpty s = Iso from to (SCons SNil) (smap proxyList s)
  where from      = Just . happly (unList s)
        to        = Just . hsingleton . toList s

some :: SList xs -> Format m i xs -> Format m i (Map [] xs)
some s f = inverse (combine s) <$> f <@> many s f

sepBy :: SList xs -> Format m i xs -> Format m i '[] -> Format m i (Map [] xs)
sepBy s f sep = sepBy1 s f sep
             <|> manyEmpty s <$> Pure (hsingleton []) 

sepBy1 :: SList xs -> Format m i xs -> Format m i '[] -> Format m i (Map [] xs)
sepBy1 s f sep = inverse (combine s) <$> f <@> many s (sep @> f)

-- | The `chainl1` combinator is used to parse a
-- left-associative chain of infix operators. 
chainl1 :: SFormat m i a -> SFormat m i b -> Iso '[a, b, a] '[a] -> SFormat m i a
chainl1 arg op f = C.foldl s f <$> arg <@> many s (op <@> arg)
  where s = SCons (SCons SNil)
