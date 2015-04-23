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

-- | A well-typed edit script that maps transforms xs values in ys values,
-- by means of insert, delete and update.
data ES f xs ys where
  -- | Inserts something new in the tree
  Ins :: f xs a -> ES f ys (Append xs zs) -> ES f ys (a ': zs)
  -- | Removes something from the original tree
  Del :: f xs a -> ES f (Append xs ys) zs -> ES f (a ': ys) zs  
  -- | Replaces something in the original tree
  Upd :: f xs a -> f ys a -> ES f (Append xs zs) (Append ys ws) -> ES f (a ': zs) (a ': ws)
  -- | Terminates the edit script
  End :: ES f '[] '[]

-- TODO probably we want to store the cost with the ETree
cost :: Metric f => ES f xs ys -> Int
cost End = 0
cost (Ins x xs) = 1 + cost xs
cost (Del x xs) = 1 + cost xs
cost (Upd f g xs) = distance f g + cost xs

-- Returns the best edit tree (least distance)
(&) :: Metric f => ES f xs ys -> ES f xs ys -> ES f xs ys
x & y = if cost x <= cost y then x else y

-- A @'View' f a@ deconstructs a value, producing a 
-- witness @f xs a@ of its constructor, with a list 
-- containing its fields.
data View f a where
  View :: f xs a -> HList xs -> View f a

-- TODO avoid proxy
diff :: (Family f, Metric f) => Proxy f -> HList xs -> HList ys -> ES f xs ys
diff _ Nil Nil = End
diff p (Cons x xs) Nil = 
  case view p x of 
    View f ys -> Del f $ diff p (happend ys xs) Nil
diff p Nil (Cons y ys) =
  case view p y of
    View g xs -> Ins g $ diff p Nil (happend xs ys)
diff p (Cons x xs) (Cons y ys) =
  case (view p x, view p y) of
    (View f fs, View g gs) -> 
      let i = Ins g $ diff p (Cons x xs) (happend gs ys) 
          d = Del f $ diff p (happend fs xs) (Cons y ys) in 
      case decEq f g of
        Nothing -> i & d
        Just Refl -> i & d & u
          where u = Upd f g $ diff p (happend fs xs) (happend gs ys)
 
----------------------------------------------------------------------------------
class Family f where
  decEq :: f xs a -> f ys b -> Maybe (a :~: b)
  string :: f xs a -> String
  view :: Proxy f -> a -> View f a

class Metric f where
  -- Laws:
  --  d x y = d y x             (symmetry)
  --  d x y >= 0                (non-negativity)
  --  d x x = 0                 (identity)
  --  d x z <= d x y + d y z    (triangle inequality)
  distance :: f xs a -> f ys a -> Int
