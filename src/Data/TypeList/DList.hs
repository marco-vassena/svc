{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.TypeList.DList (
    module Data.TypeList.Core
  , dappend
  , dsplit
  , View(..)
  , DList(..)
  , Family(..)
  , (:<:)(..)
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

class a :<: f where
  view :: Proxy f -> a -> View f a
  getElem :: Elem f a (TypesOf f)

class Family f where
  -- TODO better name
  decEq :: f xs a -> f ys b -> Maybe (a :~: b)
  
  -- Succeds only if the singleton types represents exactly the same constructor
  (=?=) :: Family f => f xs a -> f ys b -> Maybe ( a :~: b , xs :~: ys ) -- TODO: Remove Family f 

  string :: f xs a -> String
  build :: f xs a -> DList f xs -> a
  unbuild :: f xs a -> a -> Maybe (DList f xs)
  
  reifyF :: f xs a -> SList xs

--------------------------------------------------------------------------------

type family TypesOf (f :: [ * ] -> * -> *) :: [ * ]

data TList f xs where
  TNil :: TList f '[]
  TCons :: TList f xs -> TList f (x ': xs)

data Elem f x xs where
  Here :: Elem f x (x ': xs) -- Maybe x :<: f
  There :: (y :<: f) => Elem f x ys -> Elem f x (y ': ys)

