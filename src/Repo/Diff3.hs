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
  Node :: (Family f, ShowDT f sig) => f sig res -> DList f sig -> DTree f res

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

-- | The ETree datatype represents a tree-shaped well-typed edit script
data ETree f a where
  Ins :: f xs a -> EList f xs -> ETree f a
  Del :: f xs a -> EList f '[ a ] -> ETree f a
  Upd :: f xs a -> f ys a -> EList f ys -> ETree f a  -- TODO add distance

data EList f xs where
  ENil :: EList f '[]
  ConsU :: ETree f x -> EList f xs -> EList f (x ': xs)
  ConsA :: ETree f x -> EList f xs -> EList f (x ': xs)
  ConsD :: ETree f x -> EList f xs -> EList f xs

emap :: (forall x . ETree f x -> a) -> EList f xs -> [ a ]
emap _ ENil = []
emap f (ConsA x xs) = f x : emap f xs
emap f (ConsD x xs) = f x : emap f xs
emap f (ConsU x xs) = f x : emap f xs


-- TODO probably we want to store the cost with the ETree
cost :: Metric f => ETree f a -> Int
cost (Ins _ xs) = 1 + costs xs
cost (Del _ xs) = 1 + costs xs
cost (Upd x y xs) = distance x y + costs xs

costs :: Metric f => EList f xs -> Int
costs xs = sum (emap cost xs)

-- Returns the best edit tree (least distance)
(&) :: Metric f => ETree f a -> ETree f a -> ETree f a
x & y = if cost x <= cost y then x else y

-- Returns the best edit list (least distance)
(&&&) :: Metric f => EList f xs -> EList f xs -> EList f xs
xs &&& ys = if costs xs <= costs ys then xs else ys

-- TODO memoization
diff :: Metric f => DTree f a -> DTree f a -> ETree f a
diff n@(Node f xs) m@(Node g ys) =
  case decEq f g of
    Just Refl -> a & b & (Upd f g (diffs xs ys))
    Nothing -> a & b
  where a = Del f (diffs xs (dsingleton m))
        b = Ins g (diffs (dsingleton n) ys)
        
diffs :: Metric f => DList f xs -> DList f ys -> EList f ys
diffs DNil DNil = ENil
diffs DNil (DCons x xs) = ConsA (ins x) (diffs DNil xs)
diffs (DCons x xs) DNil = ConsD (ins x) (diffs xs DNil)
diffs d1@(DCons x xs) d2@(DCons y ys) = 
  case decEq' x y of
    Just Refl -> a &&& b &&& (ConsU (diff x y) (diffs xs ys))
    Nothing -> a &&& b
  where a = ConsD (ins x) (diffs xs d2)
        b = ConsA (ins y) (diffs d1 ys)
 
ins :: DTree f xs -> ETree f xs
ins (Node f xs) = Ins f (insList xs)

insList :: DList f xs -> EList f xs
insList DNil = ENil
insList (DCons x xs) = ConsA (ins x) (insList xs)

dsingleton :: DTree f a -> DList f '[ a ]
dsingleton x = DCons x DNil

decEq' :: DTree f a -> DTree f b -> Maybe (a :~: b)
decEq' (Node a xs) (Node b ys) = decEq a b

decEq'' :: Family f => ETree f a -> ETree f b -> Maybe (a :~: b)
decEq'' x y = 
  case (getTarget x, getTarget y) of
    (SF a, SF b) -> decEq a b

data SF f a where
  SF :: f xs a -> SF f a

getTarget :: ETree f a -> SF f a
getTarget (Ins f _ ) = SF f
getTarget (Del f _ ) = SF f
getTarget (Upd _ f _) = SF f

--------------------------------------------------------------------------------
-- Diff3


-- For the time being I am assuming the scripts are "aligned"
diff3 :: (Family f, Metric f) => ETree f a -> ETree f a -> ETree f a
diff3 (Upd o x xs) (Upd _ y ys)
  | distance x y == 0 = Upd o y (diffs3 xs ys) 
  | otherwise         = conflict x y
diff3 u@(Upd o x xs) (Ins y ys) = Ins y (align1 u ys)
diff3 (Ins x xs) u@(Upd o y ys) = Ins x (align2 xs u)
diff3 (Ins x xs) (Ins y ys) =
  let c = conflict x y in
  case decEq x y of
    Just Refl -> if distance x y == 0 then Ins y (diffs3 xs ys) else c
    Nothing -> c
diff3 (Del x xs) (Del y ys) = Del x (diffs3 xs ys) -- We don't check x == y since I am assuing we are aligned
diff3 (Upd o x xs) (Del y ys)
  | distance o x == 0 = Del y (diffs3 xs ys)
  | otherwise         = deletedOrChanged o y x
diff3 (Del x xs) u2@(Upd o y ys)
  | distance o y == 0 = Del x (diffs3 ys xs)
  | otherwise         = deletedOrChanged o x y 

conflict a b = error msg
  where msg = "conflict: " ++ string a ++ " <-> " ++ string b

deletedOrChanged o a b = error msg
  where msg = "conflict: " ++ deleted ++ " <-> " ++ changed
        deleted = "deleted " ++ string a
        changed = string o ++ " changed to " ++ string b

align1 :: ETree f a -> EList f xs -> EList f xs
align1 = undefined

align2 :: EList f xs -> ETree f a -> EList f xs
align2 = undefined

diffs3 :: (Family f, Metric f) => EList f xs -> EList f ys -> EList f ys
diffs3 (ConsU x xs) (ConsU y ys) = 
  case decEq'' x y of
    Just Refl -> ConsU (diff3 x y) (diffs3 xs ys)
    Nothing -> error "conflicting types" -- TODO here, down in the trees there could be matching parts
diffs3 (ConsA x xs) (ConsA y ys) =  
   case decEq'' x y of
    Just Refl -> ConsA (diff3 x y) (diffs3 xs ys)
    Nothing -> error "conflicting types" -- TODO here, down in the trees there could be matching parts
diffs3 (ConsD x xs) (ConsD y ys) =  
   case decEq'' x y of
    Just Refl -> ConsD (diff3 x y) (diffs3 xs ys)
    Nothing -> error "conflicting types" -- TODO here, down in the trees there could be matching parts
diffs3 (ConsD x xs) (ConsA y ys) = undefined
diffs3 (ConsA x xs) (ConsD y ys) = undefined

--------------------------------------------------------------------------------

class Family f where
  decEq :: f xs a -> f ys b -> Maybe (a :~: b)  -- We need to treat basic values differently
  apply :: f xs a -> DList f xs -> a
  string :: f xs a -> String

instance Show (DTree f a) where
  show (Node c args) = "Node " ++ string c ++ " [" ++ xs ++ "]"
    where xs = concat $ intersperse ", " (dmap show args)

-- A class used to collect show instances for type-lists.
class ShowDT f sig where
  
instance ShowDT f '[] where
instance (Show (DTree f a), ShowDT f xs) => ShowDT f (a ': xs) where

instance Family f => Show (ETree f a) where
  show (Ins f xs) = "Ins " ++ string f ++ " (" ++ show xs ++ ")"
  show (Del f xs) = "Del " ++ string f ++ " (" ++ show xs ++ ")"
  show (Upd x y xs) = "Upd " ++ string x ++ " " ++ string y ++ " (" ++ show xs ++ ")"

instance Family f => Show (EList f xs) where
  show ENil = "ENil"
  show (ConsA x xs) = "ConsA " ++ show x ++ " (" ++ show xs ++ ")"
  show (ConsD x xs) = "ConsD " ++ show x ++ " (" ++ show xs ++ ")"
  show (ConsU x xs) = "ConsU " ++ show x ++ " (" ++ show xs ++ ")"
