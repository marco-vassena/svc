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

import Data.HList
import Data.List
import Data.Type.Equality

-- A generic well-typed representation of a data-type
data DTree f a where
  Node :: KnownSList sig => f sig res -> DList f sig -> DTree f res

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
data ES f xs ys where
  -- Inserts something new in the tree
  Ins :: KnownSList zs => f xs a -> ES f ys (Append xs zs) -> ES f ys (a ': zs)
  -- Removes something from the original tree
  Del :: KnownSList ys => f xs a -> ES f (Append xs ys) zs -> ES f (a ': ys) zs  
  -- Replaces something in the original tree
  Upd :: (KnownSList zs, KnownSList ws) 
      => f xs a -> f ys a -> ES f (Append xs zs) (Append ys ws) -> ES f (a ': zs) (a ': ws)

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

-- Using HList
--diff :: (Family f, Metric f) => HList xs -> HList ys -> ES f xs ys
--diff Nil Nil = End
--diff (Cons x xs) Nil = Del x undefined

-- TODO memoization
diff :: (Family f, Metric f) => DTree f a -> DTree f b -> ES f '[a] '[b]
diff n@(Node f xs) m@(Node g ys) = 
  let (xss, yss) = (toSList xs, toSList ys) in
    case (rightIdentityAppend xss, rightIdentityAppend yss) of
      (Refl, Refl) -> 
        let a = Del f (diffT1 xs m)
            b = Ins g (diffT2 n ys) in
          case decEq f g of
            Just Refl -> a & b & Upd f g (diffs xs ys)
            Nothing -> a & b

diffs :: (Family f, Metric f) => DList f xs -> DList f ys -> ES f xs ys
diffs DNil DNil = End
--diffs (DCons x@(Node y ys) xs) DNil = (diffs xs DNil)
diffs n@(DCons x xs) m@(DCons y ys) = diffs n ys
  where a = diff x y +++ diffs xs ys 

diffT1 :: (Family f, Metric f) => DList f xs -> DTree f b -> ES f xs '[b]
diffT1 = undefined

diffT2 :: (Family f, Metric f) => DTree f a -> DList f ys -> ES f '[a] ys
diffT2 = undefined

-- TODO generalize the one given in Data.HList
appenedAssoc :: SList xs -> SList ys -> SList zs 
             -> SList (Append xs (Append ys zs)) :~: SList (Append (Append xs ys) zs)
appenedAssoc = undefined

instance Reify2 (ES f) where
  toSList2 End = (SNil, SNil)
  toSList2 (Ins x xs) = (s1 , SCons slist)
    where (s1, s2) = toSList2 xs
  toSList2 (Del x xs) = (SCons slist, s2)
    where (s1, s2) = toSList2 xs
  toSList2 (Upd f g xs) = (SCons slist, SCons slist)

getSList :: KnownSList xs => f xs a -> SList xs
getSList _ = slist

(+++) :: ES f xs ys -> ES f zs ws -> ES f (Append xs zs) (Append ys ws)
End +++ ys = ys
as@(Ins b bs) +++ cs = undefined

-- n@(Node f xs) m@(Node g ys) =
--  case decEq f g of
--    Just Refl -> a & b & Upd f g (diffs xs ys)
--    Nothing -> a & b
--  where a = Del f (diffs xs (dsingleton m))
--        b = Ins g (diffs (dsingleton n) ys)
        
--diffs :: (Family f, Metric f) => DList f xs -> DList f ys -> EList f ys
--diffs DNil DNil = ENil
--diffs DNil (DCons x xs) = Cons (ins x) (diffs DNil xs)
--diffs (DCons x xs) DNil = ConsD (ins x) (diffs xs DNil)
--diffs d1@(DCons x xs) d2@(DCons y ys) = a &&& b &&& Cons (diff x y) (diffs xs ys)
--  where a = ConsD (ins x) (diffs xs d2)
--        b = Cons (ins y) (diffs d1 ys)
-- 
--ins :: (Family f, Metric f) => DTree f xs -> ETree f xs
--ins (Node f xs) = Ins f (insList xs)
--
--insList :: (Family f, Metric f) => DList f xs -> EList f xs
--insList DNil = ENil
--insList (DCons x xs) = Cons (ins x) (insList xs)
--
---- An ETree a contains all the information to reconstruct
---- the target tree.
--patch :: Family f => ETree f a -> DTree f a
--patch (Ins x xs) = Node x (patchEList xs)
--patch (Del x xs) = 
--  case patchEList xs of
--    DCons d DNil -> d
--patch (Upd _ x xs) = Node x (patchEList xs)
--
--patchEList :: Family f => EList f xs -> DList f xs
--patchEList ENil = DNil
--patchEList (Cons x xs) = DCons (patch x) $ patchEList xs
--patchEList (ConsD _ xs) = patchEList xs
--    
----------------------------------------------------------------------------------
--
--dsingleton :: DTree f a -> DList f '[ a ]
--dsingleton x = DCons x DNil
--
--decEq' :: Family f => DTree f a -> DTree f b -> Maybe (a :~: b)
--decEq' (Node a xs) (Node b ys) = decEq a b
--
--decEq'' :: Family f => ETree f a -> ETree f b -> Maybe (a :~: b)
--decEq'' x y = 
--  case (getTarget x, getTarget y) of
--    (SF a, SF b) -> decEq a b
--
--data SF f a where
--  SF :: f xs a -> SF f a
--
--getTarget :: ETree f a -> SF f a
--getTarget (Ins f _ ) = SF f
--getTarget (Del _ xs) = getTarget' xs
--getTarget (Upd _ f _) = SF f
--
--getTarget' :: EList f '[ a ] -> SF f a
--getTarget' (Cons x _) = getTarget x
--getTarget' (ConsD _ xs) = getTarget' xs
--
----------------------------------------------------------------------------------
---- Diff3
--
--
---- For the time being I am assuming the scripts are "aligned"
--diff3 :: (Family f, Metric f) => ETree f a -> ETree f a -> ETree f a
--diff3 (Upd o x xs) (Upd _ y ys)
--  | distance x y == 0 = Upd o y (diffs3 xs ys) 
--  | otherwise         = conflict x y
--diff3 u@(Upd o x xs) (Ins y ys) = Ins y (align u ys)
--diff3 (Ins x xs) u@(Upd o y ys) = Ins x (align u xs)
--diff3 (Ins x xs) (Ins y ys) =
--  let c = conflict x y in
--  case decEq x y of
--    Just Refl -> if distance x y == 0 then Ins y (diffs3 xs ys) else c
--    Nothing -> c
--diff3 (Del x xs) (Del y ys) = Del x (diffs3 xs ys) -- We don't check x == y since I am assuing we are aligned
--diff3 (Upd o x xs) (Del y ys)
--  | distance o x == 0 = Del y (diffs3 xs ys)
--  | otherwise         = deletedOrChanged o y x
--diff3 (Del x xs) u2@(Upd o y ys)
--  | distance o y == 0 = Del x (diffs3 ys xs)
--  | otherwise         = deletedOrChanged o x y 
--
--conflict a b = error msg
--  where msg = "Value Conflict: " ++ string a ++ " <-> " ++ string b
--
--deletedOrChanged o a b = error msg
--  where msg = "Shape conflict: " ++ deleted ++ " <-> " ++ changed
--        deleted = "deleted " ++ string a
--        changed = string o ++ " changed to " ++ string b
--
--align :: (Metric f, Family f) => ETree f a -> EList f xs -> EList f xs
--align e ENil = error $ "Could Not Align ETree " ++ show e ++ "\nInvalid EditTree?"
--align e (Cons e' es) = 
--  case decEq'' e e' of
--    Just Refl -> Cons (diff3 e e') es
--    Nothing -> error "conflicting types"
--align e (ConsD e' es) = 
--  case decEq'' e e' of
--    Just Refl -> ConsD (diff3 e e') es
--    Nothing -> error "conflicting types"
--
--diffs3 :: (Family f, Metric f) => EList f xs -> EList f ys -> EList f ys
--diffs3 (Cons x xs) (Cons y ys) = 
--  case decEq'' x y of
--    Just Refl -> Cons (diff3 x y) (diffs3 xs ys)
--    Nothing -> error "conflicting types" -- TODO here, down in the trees there could be matching parts
--diffs3 (ConsD x xs) (ConsD y ys) =  
--   case decEq'' x y of
--    Just Refl -> ConsD (diff3 x y) (diffs3 xs ys)
--    Nothing -> error "conflicting types" -- TODO here, down in the trees there could be matching parts
--
----------------------------------------------------------------------------------
--
class Family f where
  decEq :: f xs a -> f ys b -> Maybe (a :~: b)
  apply :: f xs a -> DList f xs -> a
  string :: f xs a -> String

--instance Family f => Show (DTree f a) where
--  show (Node c args) = "Node " ++ string c ++ " [" ++ xs ++ "]"
--    where xs = concat $ intersperse ", " (dmap show args)
--
--instance Family f => Show (ETree f a) where
--  show (Ins f xs) = "Ins " ++ string f ++ " (" ++ show xs ++ ")"
--  show (Del f xs) = "Del " ++ string f ++ " (" ++ show xs ++ ")"
--  show (Upd x y xs) = "Upd " ++ string x ++ " " ++ string y ++ " (" ++ show xs ++ ")"
--
--instance Family f => Show (EList f xs) where
--  show ENil = "ENil"
--  show (Cons x xs) = "Cons " ++ show x ++ " (" ++ show xs ++ ")"
--  show (ConsD x xs) = "ConsD " ++ show x ++ " (" ++ show xs ++ ")"
