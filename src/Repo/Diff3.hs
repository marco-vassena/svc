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

-- TODO use this in Data.HList instead of :++:
type (:++:) = Append

-- TODO for the ES datatype we could
-- 1) Include Cpy (a special case of Upd), which might make the code for diff3 easier.
-- 2) Consider Upd which different resulting types.
--      When a ~ b -> cost = distance
--      otherwise -> cost = 1

-- | A well-typed edit script that maps transforms xs values in ys values,
-- by means of insert, delete and update.
data ES f xs ys where
  -- | Inserts something new in the tree
  Ins :: f xs a -> ES f ys (xs :++: zs) -> ES f ys (a ': zs)
  -- | Removes something from the original tree
  Del :: f xs a -> ES f (xs :++: ys) zs -> ES f (a ': ys) zs  
  -- | Replaces something in the original tree
  Upd :: f xs a -> f ys a -> ES f (xs :++: zs) (ys :++: ws) -> ES f (a ': zs) (a ': ws)
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
  View :: f xs a -> DList f xs -> View f a

data DList f xs where
  DNil :: DList f '[]
  DCons :: (x :<: f) => x -> DList f xs -> DList f (x ': xs)

dappend :: DList f xs -> DList f ys -> DList f (xs :++: ys)
dappend DNil ys = ys
dappend (DCons x xs) ys = DCons x (dappend xs ys)


-- Represents the fact that a type a belongs to a particular
-- family of mutually recursive data-types
class a :<: f where
  view :: Proxy f -> a -> View f a

-- TODO memoization
diff :: (Family f, Metric f) => Proxy f -> DList f xs -> DList f ys -> ES f xs ys
diff _ DNil DNil = End
diff p (DCons x xs) DNil = 
  case view p x of 
    View f ys -> Del f $ diff p (dappend ys xs) DNil
diff p DNil (DCons y ys) =
  case view p y of
    View g xs -> Ins g $ diff p DNil (dappend xs ys)
diff p (DCons x xs) (DCons y ys) =
  case (view p x, view p y) of
    (View f fs, View g gs) -> 
      let i = Ins g $ diff p (DCons x xs) (dappend gs ys) 
          d = Del f $ diff p (dappend fs xs) (DCons y ys) in 
      case decEq f g of
        Nothing -> i & d
        Just Refl -> i & d & u
          where u = Upd f g $ diff p (dappend fs xs) (dappend gs ys)
 
data ES3 f xs ys ws where
  Ins1 :: f xs a -> ES3 f ys (xs :++: zs) ws -> ES3 f ys (a ': zs) ws
  Ins2 :: f xs a -> ES3 f ys ws (xs :++: zs) -> ES3 f ys ws (a ': zs)
  Del3 :: f xs a -> ES3 f (xs :++:  ys) zs ws -> ES3 f (a ': ys) zs ws
  Upd3 :: f xs a -> f ys a -> ES3 f (xs :++: zs) (ys :++: ws) (ys :++: us) 
       -> ES3 f (a ': zs) (a ': ws) (a ': us)
  End3 :: ES3 f '[] '[] '[]

-- I am assuming we are aligned
diff3 :: (Family f, Metric f) => ES f xs ys -> ES f xs ws -> ES3 f xs ys zs
diff3 = undefined

conflict :: Family f => f xs a -> f ys b -> t
conflict x y = error $ "Value conflict: " ++ string x ++ " " ++ string y

----------------------------------------------------------------------------------
class Family f where
  decEq :: f xs a -> f ys b -> Maybe (a :~: b)
  string :: f xs a -> String
  build :: f xs a -> DList f xs -> a

class Metric f where
  -- Laws:
  --  d x y = d y x             (symmetry)
  --  d x y >= 0                (non-negativity)
  --  d x x = 0                 (identity)
  --  d x z <= d x y + d y z    (triangle inequality)
  distance :: f xs a -> f ys a -> Int

--------------------------------------------------------------------------------
instance Family f => Show (ES f xs ys) where
  show End = "End"
  show (Ins x xs) = "Ins " ++ string x ++ " $ " ++ show xs
  show (Del x xs) = "Del " ++ string x ++ " $ " ++ show xs
  show (Upd f g xs) = "Upd " ++ string f ++ " " ++ string g ++ " $ " ++ show xs
