{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.TypeList.DList (
    module Data.TypeList.Core
  , module Data.TypeList.SList
  , dappend
  , dsplit
  , dHead
  , TreeLike(..)
  , DList(..)
  , DTree(..)
  , toDList
  , reifyArgs
  , TList(..)
  , KnownTList(..)
  , tyEq
  , tysEq
  , F
  , decEq
  , Metric(..)
  , showTy
  ) where

import Data.TypeList.Core
import Data.TypeList.SList
import Data.TypeList.TList
import Data.Proxy
import Data.Typeable

-- TODO merge TreeLike and Metric in Diff

-- Represents the fact that a type a belongs to a particular
-- family of mutually recursive data-types
-- TODO can we abstract over Int and just use anything Numeric, Ord
class TreeLike a => Metric a where
  -- Laws:
  --  d x y = d y x             (symmetry)
  --  d x y >= 0                (non-negativity)
  --  d x x = 0                 (identity)
  --  d x z <= d x y + d y z    (triangle inequality)
  distance :: F xs a -> F ys a -> Int

data DList xs where
  DNil :: DList '[]
  DCons :: Metric x => DTree (FamilyOf x) x -> DList xs -> DList (x ': xs)

data DTree f x where
  Node :: f xs x -> DList xs -> DTree f x

dappend :: DList xs -> DList ys -> DList (xs :++: ys)
dappend DNil ys = ys
dappend (DCons x xs) ys = DCons x (dappend xs ys)

dsplit :: SList xs -> DList (xs :++: ys) -> (DList xs, DList ys)
dsplit SNil ds = (DNil, ds)
dsplit (SCons s) (DCons x ds) = (DCons x ds1, ds2)
  where (ds1, ds2) = dsplit s ds

dHead :: DList (a ': xs) -> DTree (FamilyOf a) a
dHead (DCons x _) = x

--------------------------------------------------------------------------------

-- Convenient synonym
type F xs a = (FamilyOf a) xs a

-- Alternative synonym for new change in FamilyOf :: * -> [ * ] -> *
-- type F xs a = (FamilyOf a) xs

class Typeable a => TreeLike a where
  -- TODO do we actually need * ? I don't think so
  -- we can get the right order with a type synonym
  type FamilyOf a :: [ * ] -> * -> *

  (=?=) :: (FamilyOf a) xs a -> (FamilyOf a) ys a -> Maybe (xs :~: ys)

  string :: (FamilyOf a) xs a -> String

  argsTy :: (FamilyOf a) xs a -> TList xs

  toDTree :: a -> DTree (FamilyOf a) a
  fromDTree :: DTree (FamilyOf a) a -> a


outputTy :: Typeable a => f xs a -> TList '[ a ]
outputTy _ = TCons Proxy TNil

reifyArgs :: TreeLike a => (FamilyOf a) xs a -> SList xs
reifyArgs = toSList . argsTy

toDList :: Metric a => a -> DList '[ a ]
toDList x = DCons (toDTree x) DNil

-- TODO rename to sameOutputTy
-- TODO maybe move to Diff
decEq :: (TreeLike a, TreeLike b) => F xs a -> F ys b -> Maybe (a :~: b)
decEq x y = tyEq (outputProxy x) (outputProxy y)

outputProxy :: f xs a -> Proxy a
outputProxy _ = Proxy

familyProxy :: f xs a -> Proxy f
familyProxy _ = Proxy

showTy :: Typeable a => Proxy a -> String
showTy = show . typeRep
--------------------------------------------------------------------------------
