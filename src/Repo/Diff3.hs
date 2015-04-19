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

import Data.List
import Data.Type.Equality

-- A generic well-typed representation of a data-type
data DTree f a where
  -- TODO you could remove Family f from here since f is exposed.
  Node :: (Family f, ShowDT f sig) => f sig res -> DList (DTree f) sig -> DTree f res

-- A typed list that contains the children (arguments) of a constructor.
data DList f xs where
  DNil :: DList f '[]
  DCons :: f a -> DList f as -> DList f (a ': as)

dmap :: (forall x . f x -> a) -> DList f xs -> [ a ]
dmap f DNil = []
dmap f (DCons x xs) = f x : dmap f xs

class TreeLike f a where
  toTree :: a -> DTree f a
  fromTree :: DTree f a -> a

--------------------------------------------------------------------------------
class Metric f where
  distance :: f xs a -> f ys a -> Double

-- | The ETree datatype represents a tree-shaped well-typed edit script
data ETree a where
  Ins :: Family f => f xs a -> EList ETree xs -> ETree a
  Del :: Family f => f xs a -> EList ETree '[ a ] -> ETree a
  Upd :: (Family f, Metric f) => f xs a -> f ys a -> EList ETree ys -> ETree a  -- TODO add distance

data EList f xs where
  ENil :: EList f '[]
  ConsU :: f x -> EList f xs -> EList f (x ': xs)
  ConsA :: f x -> EList f xs -> EList f (x ': xs)
  ConsD :: f x -> EList f xs -> EList f xs

emap :: (forall x . f x -> a) -> EList f xs -> [ a ]
emap _ ENil = []
emap f (ConsA x xs) = f x : emap f xs
emap f (ConsD x xs) = f x : emap f xs
emap f (ConsU x xs) = f x : emap f xs


-- TODO probably we want to store the cost with the ETree
cost :: ETree a -> Double
cost (Ins _ xs) = 1 + costs xs
cost (Del _ xs) = 1 + costs xs
cost (Upd x y xs) = distance x y + costs xs

costs :: EList ETree xs -> Double
costs xs = sum (emap cost xs)

-- Returns the best edit tree (least distance)
(&) :: ETree a -> ETree a -> ETree a
x & y = if cost x <= cost y then x else y

-- Returns the best edit list (least distance)
(&&&) :: EList ETree xs -> EList ETree xs -> EList ETree xs
xs &&& ys = if costs xs <= costs ys then xs else ys

-- TODO memoization
diff :: Metric f => DTree f a -> DTree f a -> ETree a
diff n@(Node f xs) m@(Node g ys) =
  case decEq f g of
    Just Refl -> a & b & (Upd f g (diffs xs ys))
    Nothing -> a & b
  where a = Del f (diffs xs (dsingleton m))
        b = Ins g (diffs (dsingleton n) ys)
        
diffs :: Metric f => DList (DTree f) xs -> DList (DTree f) ys -> EList ETree ys
diffs DNil DNil = ENil
diffs DNil (DCons x xs) = ConsA (ins x) (diffs DNil xs)
diffs (DCons x xs) DNil = ConsD (ins x) (diffs xs DNil)
diffs d1@(DCons x xs) d2@(DCons y ys) = 
  case decEq' x y of
    Just Refl -> a &&& b &&& (ConsU (diff x y) (diffs xs ys))
    Nothing -> a &&& b
  where a = ConsD (ins x) (diffs xs d2)
        b = ConsA (ins y) (diffs d1 ys)
 
ins :: DTree f xs -> ETree xs
ins (Node f xs) = Ins f (insList xs)

insList :: DList (DTree f) xs -> EList ETree xs
insList DNil = ENil
insList (DCons x xs) = ConsA (ins x) (insList xs)

dsingleton :: f a -> DList f '[ a ]
dsingleton x = DCons x DNil

decEq' :: DTree f a -> DTree f b -> Maybe (a :~: b)
decEq' (Node a xs) (Node b ys) = decEq a b

--------------------------------------------------------------------------------

class Family f where
  decEq :: f xs a -> f ys b -> Maybe (a :~: b)  -- We need to treat basic values differently
  apply :: f xs a -> DList (DTree f) xs -> a
  string :: f xs a -> String

instance Show (DTree f a) where
  show (Node c args) = "Node " ++ string c ++ " [" ++ xs ++ "]"
    where xs = concat $ intersperse ", " (dmap show args)

-- A class used to collect show instances for type-lists.
class ShowDT f sig where
  
instance ShowDT f '[] where
instance (Show (DTree f a), ShowDT f xs) => ShowDT f (a ': xs) where

instance Show (ETree a) where
  show (Ins f xs) = unwords ["Ins", string f, showLikeList xs]
  show (Del f xs) = unwords ["Del", string f, showLikeList xs]
  show (Upd x y xs) = unwords ["Upd", string x, string y, showLikeList xs]
  
showLikeList :: EList ETree xs -> String
showLikeList args = "[" ++ concat xss ++ "]"
  where xss = intersperse ", " (emap show args)
