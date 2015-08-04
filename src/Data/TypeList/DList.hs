{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}

module Data.TypeList.DList (
    module Data.TypeList.Core
  , module Data.TypeList.SList
  , dappend
  , dsplit
  , View(..)
  , DList(..)
  , Elem(..)
  , Family(..)
  , (:<:)(..)
  , In(..)
  , TypesOf
  , decEq
  , reifyArgs
  , TList(..)
  , KnownTList(..)
  , proxyOfTL
  , tyEq
  ) where

import Data.TypeList.Core
import Data.TypeList.SList
import Data.Proxy
import Data.Type.Equality

-- DList and similar

-- TODO maybe move to Data.DList
data DList f xs where
  DNil :: DList f '[]
  DCons :: (x :<: f) => x -> DList f xs -> DList f (x ': xs)

dappend :: DList f xs -> DList f ys -> DList f (xs :++: ys)
dappend DNil ys = ys
dappend (DCons x xs) ys = DCons x (dappend xs ys)

dsplit :: SList xs -> DList f (xs :++: ys) -> (DList f xs, DList f ys)
dsplit SNil ds = (DNil, ds)
dsplit (SCons s) (DCons x ds) = (DCons x ds1, ds2)
  where (ds1, ds2) = dsplit s ds

--------------------------------------------------------------------------------
-- TODO can we avoid View at all? rather prefer the 
-- DList and DTree safer version ?

-- A @'View' f a@ deconstructs a value, producing a 
-- witness @f xs a@ of its constructor, with a list 
-- containing its fields.
data View f a where
  View :: f xs a -> DList f xs -> View f a

-- Belongs to relation
class a :<: (f :: [ * ] -> * -> *) where
  view :: Proxy f -> a -> View f a
  getElem :: Proxy f -> Proxy a -> Elem f a (TypesOf f)

class Family f where
  
  -- Succeds only if the singleton types represents exactly the same constructor
  (=?=) :: f xs a -> f ys b -> Maybe ( a :~: b , xs :~: ys )

  -- TODO
  -- Can we use DList and DTree instead of single DList with Maybe?
  -- Since we are not already putting effort in saving space,
  -- it is better to provide an interface as safe as possible, for the proof of concept.
  build :: f xs a -> DList f xs -> a
  unbuild :: f xs a -> a -> Maybe (DList f xs)
  
  string :: f xs a -> String

  -- TODO insert instead
  argsTy :: f xs a -> TList f xs
  outputTy :: f xs a -> TList f '[ a ]


reifyArgs :: Family f => f xs a -> SList xs
reifyArgs = toSList . argsTy

-- TODO rename to sameOutputTy
decEq :: (a :<: f, b :<: f) => f xs a -> f ys b -> Maybe (a :~: b)
decEq x y = tyEq (familyProxy x) Proxy Proxy

outputProxy :: f xs a -> Proxy a
outputProxy _ = Proxy

familyProxy :: f xs a -> Proxy f
familyProxy _ = Proxy

--------------------------------------------------------------------------------
-- The only important requirement for consistency
-- is that the list returned is actually a set.
type family TypesOf (f :: [ * ] -> * -> *) :: [ * ]

data Elem f x xs where
  Here :: Elem f x (x ': xs) -- Maybe x :<: f
  There :: (y :<: f) => Elem f x ys -> Elem f x (y ': ys)

-- TODO I just hope that all these Proxy won't make problems
tyEq :: (a :<: f, b :<: f) => Proxy f -> Proxy a -> Proxy b -> Maybe (a :~: b)
tyEq p x y = cmp (getElem p x) (getElem p y)
  where cmp :: Elem f a xs -> Elem f b xs -> Maybe (a :~: b)
        cmp Here Here = Just Refl
        cmp (There i) (There j) = cmp i j
        cmp _ _ = Nothing

--------------------------------------------------------------------------------

-- TODO with some type features it should be possible
-- to automatically inject the proof, similarly to KnownList
-- However the problem at call sites is that there are overlapping
-- matching instances. Can we rewrite them to be exclusive?
class In f x xs where
  -- TODO do we need the proxy ?
  isIn :: Proxy f -> Proxy x -> SList xs -> Elem f x xs

instance In f x (x ': xs) where
  isIn _ _ _ = Here

instance (y :<: f, In f x ys) => In f x (y ': ys) where
  isIn p1 p2 (SCons s)= There $ isIn p1 p2 s

--------------------------------------------------------------------------------
-- TODO move to its own module

data TList f xs where
  TNil :: TList f '[]
  TCons :: (x :<: f) => Proxy x -> TList f xs -> TList f (x ': xs)

instance Reify (TList f) where
  toSList TNil = SNil
  toSList (TCons _ t) = SCons (toSList t)

proxyOfTL :: TList f xs -> Proxy f
proxyOfTL _ = Proxy

class KnownTList f xs where
  tlist :: TList f xs

instance KnownTList f '[] where
  tlist = TNil

instance (x :<: f, KnownTList f xs) => KnownTList f (x ': xs) where
  tlist = TCons Proxy tlist
--------------------------------------------------------------------------------
