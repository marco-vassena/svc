{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}

module Data.DiffUtils.Diff.DList where

import Data.TypeList.Core
import Data.TypeList.SList
import Data.TypeList.TList
import Data.Proxy
import Data.Typeable

-- | Mutually-recursive _well-typed_ heterogeneous rose-trees.
data DList xs where
  DNil :: DList '[]
  DCons :: Diff x => DTree x -> DList xs -> DList (x ': xs)

data DTree x where
  -- | It represents a constructor applied to its fields, also
  -- encoded as @DTree@.
  Node :: F xs x -> DList xs -> DTree x

-- | Appends two @DList@.
dappend :: DList xs -> DList ys -> DList (xs :++: ys)
dappend DNil ys = ys
dappend (DCons x xs) ys = DCons x (dappend xs ys)

-- | Splits in two parts a @DList@.
dsplit :: SList xs -> DList (xs :++: ys) -> (DList xs, DList ys)
dsplit SNil ds = (DNil, ds)
dsplit (SCons s) (DCons x ds) = (DCons x ds1, ds2)
  where (ds1, ds2) = dsplit s ds

-- | Returns the first element of a list.
dHead :: DList (a ': xs) -> DTree a
dHead (DCons x _) = x

--------------------------------------------------------------------------------

-- Convenient synonym 
type F xs a = (FamilyOf a) xs a

-- | This class contains the methods necessary to diff and merge data-types.
-- In principle w
class Typeable a => Diff a where

  -- | FamilyOf a is the type of the data type that
  -- represents a constructors.
  -- The last * is a, it is redundant, but avoids ambiguity issues.
  type FamilyOf a :: [ * ] -> * -> *

  -- | Returns Just Refl iff the two constructors are 
  -- exactly the same.
  (=?=) :: F xs a -> F ys a -> Maybe (xs :~: ys)

  -- | A string representation of each constructor
  string :: F xs a -> String

  -- | Produces Proxy types for the arguments of the constructors.
  -- It requires that every argument is also typeable.
  argsTy :: F xs a -> TList xs
  
  -- | Metric Laws:
  --
  -- * d x y = d y x             (symmetry)
  -- * d x y >= 0                (non-negativity)
  -- * d x x = 0                 (identity)
  -- * d x z <= d x y + d y z    (triangle inequality)
  distance :: F xs a -> F ys a -> Double

  -- | Converts a raw value to DTree representation
  toDTree :: a -> DTree a

  -- | Converts the DTree representation back to raw value
  fromDTree :: DTree a -> a

outputTy :: Typeable a => f xs a -> TList '[ a ]
outputTy _ = TCons Proxy TNil

-- | Returns a singleton type of a constructor's field types.
reifyArgs :: Diff a => F xs a -> SList xs
reifyArgs = toSList . argsTy

toDList :: Diff a => a -> DList '[ a ]
toDList x = DCons (toDTree x) DNil

fromDList :: Diff a => DList '[ a ] -> a
fromDList (DCons x DNil) = fromDTree x

-- | Checks whether the two constructors belong to the same data type.
decEq :: (Diff a, Diff b) => F xs a -> F ys b -> Maybe (a :~: b)
decEq x y = tyEq Proxy Proxy

-- | Returns a string representation of a type.
showTy :: Typeable a => Proxy a -> String
showTy = show . typeRep

--------------------------------------------------------------------------------
