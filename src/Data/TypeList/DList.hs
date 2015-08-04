{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-} -- For automatic inj'ion
{-# LANGUAGE OverlappingInstances #-}

module Data.TypeList.DList (
    module Data.TypeList.Core
  , module Data.TypeList.SList
  , dappend
  , dsplit
  , dHead
  , DList(..)
  , DTree(..)
  , toDList
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
  , tysEq
  , inject
  ) where

import Data.TypeList.Core
import Data.TypeList.SList
import Data.TypeList.HList
import Data.Proxy
import Data.Type.Equality

data DList f xs where
  DNil :: DList f '[]
  DCons :: (x :<: f) => DTree f x -> DList f xs -> DList f (x ': xs)

data DTree f x where
  Node :: f xs x -> DList f xs -> DTree f x

dappend :: DList f xs -> DList f ys -> DList f (xs :++: ys)
dappend DNil ys = ys
dappend (DCons x xs) ys = DCons x (dappend xs ys)

dsplit :: SList xs -> DList f (xs :++: ys) -> (DList f xs, DList f ys)
dsplit SNil ds = (DNil, ds)
dsplit (SCons s) (DCons x ds) = (DCons x ds1, ds2)
  where (ds1, ds2) = dsplit s ds

dHead :: DList f (a ': xs) -> DTree f a
dHead (DCons x _) = x

--------------------------------------------------------------------------------

-- Belongs to relation
class a :<: (f :: [ * ] -> * -> *) where
  toDTree :: a -> DTree f a
  fromDTree :: DTree f a -> a
  getElem :: Proxy f -> Elem f a (TypesOf f)
  -- TODO can we use a single proxy? Proxy (a ,f) and store this in TList?
  stringOfTy :: Proxy a -> Proxy f -> String

toDList :: (a :<: f) => a -> DList f '[ a ]
toDList x = DCons (toDTree x) DNil

class Family f where
  -- Succeds only if the singleton types represents exactly the same constructor
  (=?=) :: f xs a -> f ys b -> Maybe (a :~: b , xs :~: ys)

  string :: f xs a -> String

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

-- Computes decidable type equality for types belonging to a certain
-- family of recursive data types.
-- It requires a time proportional to the number types that form the family,
-- but for all practical purposes it should be considered as constant time,
-- since their number is fixed at compile time and typically small. 
tyEq :: (a :<: f, b :<: f) => Proxy f -> Proxy a -> Proxy b -> Maybe (a :~: b)
tyEq p x y = cmp (getElem p) (getElem p)
  where cmp :: Elem f a xs -> Elem f b xs -> Maybe (a :~: b)
        cmp Here Here = Just Refl
        cmp (There i) (There j) = cmp i j
        cmp _ _ = Nothing

tysEq :: Proxy f -> TList f xs -> TList f ys -> Maybe (xs :~: ys)
tysEq p TNil TNil = Just Refl
tysEq p (TCons x xs) (TCons y ys) =
  case (tyEq p x y, tysEq p xs ys) of
    (Just Refl, Just Refl) -> Just Refl
    _ -> Nothing
tysEq _ _ _ = Nothing

instance Show (Elem f x xs) where
  show Here = "Here"
  show (There Here) = "There Here"
  show (There i) = "There (" ++ show i ++ ")"

--------------------------------------------------------------------------------

-- This type class automatically produce Elem proofs
-- for type level lists xs instantiated with ground types.
-- It requires OverlappingInstances, but the more
-- specific instance is always properly chosen.
class In f x xs where
  inj' :: Proxy f -> Elem f x xs

instance In f x (x ': xs) where
  inj' _  = Here

instance (y :<: f, In f x ys) => In f x (y ': ys) where
  inj' p1 = There $ inj' p1 

inject :: In f x (TypesOf f) => Elem f x (TypesOf f)
inject = inj' Proxy

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
