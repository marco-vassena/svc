{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Repo.Diff3 where

import Data.Proxy
import Data.HList
import Data.List
import Data.Type.Equality

-- A generic well-typed representation of a data-type
data DTree f a where
  Node :: f sig res -> DList f sig -> DTree f res

-- A typed list that contains the children (arguments) of a constructor.
data DList f xs where
  DNil :: DList f '[]
  DCons :: DTree f a -> DList f as -> DList f (a ': as)

dmap :: (forall x . DTree f x -> a) -> DList f xs -> [ a ]
dmap f DNil = []
dmap f (DCons x xs) = f x : dmap f xs

class TreeLike f a where
  toTree :: a -> DTree f a
  fromTree :: DTree f a -> a

--------------------------------------------------------------------------------
class Metric f where
  distance :: f xs a -> f ys a -> Int

data ES f xs ys where
  -- Inserts something new in the tree
  Ins :: f xs a -> ES f ys (Append xs zs) -> ES f ys (a ': zs)
  -- Removes something from the original tree
  Del :: f xs a -> ES f (Append xs ys) zs -> ES f (a ': ys) zs  
  -- Replaces something in the original tree
  Upd :: f xs a -> f ys a -> ES f (Append xs zs) (Append ys ws) -> ES f (a ': zs) (a ': ws)
  -- Terminates the edit script
  End :: ES f '[] '[]

-- TODO probably we want to store the cost with the ETree
cost :: Metric f => ES f xs ys -> Int
cost = undefined 

-- Returns the best edit tree (least distance)
(&) :: Metric f => ES f xs ys -> ES f xs ys -> ES f xs ys
x & y = if cost x <= cost y then x else y

instance Reify (DList f) where
  toSList DNil = SNil
  toSList (DCons _ xs) = SCons (toSList xs)

data View f a where
  View :: f xs a -> FList f xs -> View f a

data FList f xs where
  FNil :: FList f '[]
  FCons :: x -> FList f xs -> FList f (x ': xs)

fappend :: FList f xs -> FList f ys -> FList f (Append xs ys)
fappend FNil ys = ys
fappend (FCons x xs) ys = FCons x (fappend xs ys)

-- TODO avoid proxy
diff :: (Family f, Metric f) => Proxy f -> FList f xs -> FList f ys -> ES f xs ys
diff _ FNil FNil = End
diff p (FCons x xs) FNil = 
  case view p x of 
    View f ys -> Del f $ diff p (fappend ys xs) FNil
diff p FNil (FCons y ys) =
  case view p y of
    View g xs -> Ins g $ diff p FNil (fappend xs ys)
diff p (FCons x xs) (FCons y ys) =
  case (view p x, view p y) of
    (View f fs, View g gs) -> 
      let i = Ins g $ diff p (FCons x xs) (fappend gs ys) 
          d = Del f $ diff p (fappend fs xs) (FCons y ys) in 
      case decEq f g of
        Nothing -> i & d
        Just Refl -> i & d & u
          where u = Upd f g $ diff p (fappend fs xs) (fappend gs ys)
 
----------------------------------------------------------------------------------
class Family f where
  decEq :: f xs a -> f ys b -> Maybe (a :~: b)
  apply :: f xs a -> DList f xs -> a
  string :: f xs a -> String
  view :: Proxy f -> a -> View f a
