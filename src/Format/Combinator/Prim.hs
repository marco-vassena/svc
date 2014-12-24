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
        <|> allEmpty s <$> unit

-- | This isomorphism produces an @'HList'@ of empty lists.
-- When unapplied it succeeds only if the given lists are all empty.
allEmpty :: SList xs -> Iso '[] (Map [] xs)
allEmpty s = Iso (\_ -> empty s) (to s) SNil (smap proxyList s)
  where empty :: SList xs -> Maybe (HList (Map [] xs))
        empty SNil      = Just Nil
        empty (SCons s) = empty s >>= return . (Cons [])

        to :: SList xs -> HList (Map [] xs) -> Maybe (HList '[])
        to SNil Nil               = Just Nil
        to (SCons s) (Cons [] hs) = to s hs >> Just Nil
        to (SCons s) _            = Nothing

some :: SList xs -> Format m i xs -> Format m i (Map [] xs)
some s f = inverse (combine s) <$> f <@> many s f

sepBy :: SList xs -> Format m i xs -> Format m i '[] -> Format m i (Map [] xs)
sepBy s f sep = sepBy1 s f sep
             <|> allEmpty s <$> unit

sepBy1 :: SList xs -> Format m i xs -> Format m i '[] -> Format m i (Map [] xs)
sepBy1 s f sep = inverse (combine s) <$> f <@> many s (sep @> f)

-- | The `chainl1` combinator is used to parse a
-- left-associative chain of infix operators. 
chainl1 :: SFormat m i a -> SFormat m i b -> Iso '[a, b, a] '[a] -> SFormat m i a
chainl1 arg op f = C.foldl s f <$> arg <@> many s (op <@> arg)
  where s = SCons (SCons SNil)
