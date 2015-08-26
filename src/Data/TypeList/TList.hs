{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

-- | This module defines a list of types that can be compared at runtime.

module Data.TypeList.TList (
  module Data.TypeList.SList
  , TList(..)
  , tyEq
  , tysEq
  , KnownTList(..)
  ) where

import Data.Typeable
import Data.TypeList.SList

-- A list of Typeable types.
-- Proxys are stored for convenience.:w
data TList xs where
  TNil :: TList '[]
  TCons :: Typeable x => Proxy x -> TList xs -> TList (x ': xs)

-- Decidable runtime equality between types.
tyEq :: (Typeable a, Typeable b) => Proxy a -> Proxy b -> Maybe (a :~: b)
tyEq _ _ = eqT

-- Decidable runtime equality between two lists of types.
tysEq :: TList xs -> TList ys -> Maybe (xs :~: ys)
tysEq TNil TNil = Just Refl
tysEq (TCons x xs) (TCons y ys) =
  case (tyEq x y, tysEq xs ys) of
    (Just Refl, Just Refl) -> Just Refl
    _ -> Nothing
tysEq _ _ = Nothing


--------------------------------------------------------------------------------

class KnownTList xs where
  -- | Automatically builds a @TList@ for list of types known at compile-time
  tlist :: TList xs

instance KnownTList '[] where
  tlist = TNil

instance (Typeable x, KnownTList xs) => KnownTList (x ': xs) where
  tlist = TCons Proxy tlist

--------------------------------------------------------------------------------

instance Reify TList where
  toSList TNil = SNil
  toSList (TCons _ t) = SCons (toSList t)
