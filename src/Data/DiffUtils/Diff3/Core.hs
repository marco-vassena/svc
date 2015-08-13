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

module Data.DiffUtils.Diff3.Core where

import Data.TypeList.DList
import Data.Type.Equality
import Data.DiffUtils.Diff

-- An edit script @ES3 xs@ represents a merged edit script.
-- It is well-typed with respect to the source object, but
-- it may be ill-typed with respect to the source object,
-- or it might contain value-related conflicts.
data ES3 xs where
  -- | Inserts something new in the tree
  Ins3 :: Metric a => F xs a -> ES3 ys -> ES3 ys
  -- | Removes something from the original tree
  Del3 :: Metric a => F xs a -> ES3 (xs :++: ys) -> ES3 (a ': ys)
  -- | Replaces something in the original tree
  Upd3 :: Metric a => F xs a -> F ys a -> ES3 (xs :++: zs) -> ES3 (a ': zs)
  -- | A conflict between the two edit script
  Cnf3 :: VConflict -> ES3 xs -> ES3 ys -- TODO remark that it is not worth to make this case well-typed
  -- | Terminates the edit script
  End3 :: ES3 '[]

-------------------------------------------------------------------------------- 

-- It represents value related conflicts.
-- Each constructor denotes the edits that caused the conflict.
data VConflict where
  InsIns :: (Metric a, Metric b) => F xs a -> F ys b -> VConflict
  UpdDel :: Metric a => F xs a -> F ys a -> VConflict
  DelUpd :: Metric a => F xs a -> F ys a -> VConflict
  UpdUpd :: Metric a => F xs a -> F ys a -> F zs a -> VConflict

-- Collects the conflict that may be present in the edit script.
getVConflicts :: ES3 xs -> [VConflict]
getVConflicts (Upd3 _ _ e) = getVConflicts e
getVConflicts (Ins3 _ e) = getVConflicts e
getVConflicts (Del3 _ e) = getVConflicts e
getVConflicts (Cnf3 c e) = c : getVConflicts e
getVConflicts End3 = []

--------------------------------------------------------------------------------

-- Merges two ES scripts in an ES3 script.
merge3 :: ES xs ys -> ES xs zs -> ES3 xs
merge3 (Upd o x e1) (Upd o' y e2) = 
  case aligned o o' of
    (Refl, Refl) -> 
      case (o =?= x, o' =?= y, x =?= y) of
        (Just Refl, _, _) -> Upd3 o y (merge3 e1 e2) -- Id1
        (_, Just Refl, _) -> Upd3 o x (merge3 e1 e2) -- Id2
        (_, _, Just Refl) -> Upd3 o x (merge3 e1 e2) -- Idem
        (_, _, _        ) -> Cnf3 (UpdUpd o x y) (merge3 e1 e2)
merge3 (Upd o x e1) (Del o' e2) =
  case aligned o o' of
    (Refl, Refl) -> 
      case o =?= x of
        Just Refl -> Del3 o (merge3 e1 e2) -- Id1
        Nothing   -> Cnf3 (UpdDel o x) (merge3 e1 e2)
merge3 (Del o e1) (Upd o' y e2) = 
  case aligned o o' of
    (Refl, Refl) -> 
      case o' =?= y of
        Just Refl -> Del3 o (merge3 e1 e2) -- Id2
        Nothing   -> Cnf3 (DelUpd o y) (merge3 e1 e2)
merge3 (Del x e1) (Del y e2) =
  case aligned x y of
    (Refl, Refl) -> Del3 x (merge3 e1 e2) -- Idem
merge3 (Ins x e1) (Ins y e2) =
  case decEq x y of -- TODO can we abstract over this pattern
    Just Refl ->
      case x =?= y of
        Just Refl -> Ins3 x (merge3 e1 e2) -- Idem
        Nothing           -> Cnf3 (InsIns x y) (merge3 e1 e2)
    Nothing           -> Cnf3 (InsIns x y) (merge3 e1 e2)
merge3 (Ins x e1) e2 = Ins3 x (merge3 e1 e2) -- Id2
merge3 e1 (Ins y e2) = Ins3 y (merge3 e1 e2) -- Id1
merge3 End End = End3

-- Checks whether the two witnesses are the same,
-- and fails if this is not the case.
aligned :: (Metric a, Metric b) => F xs a -> F ys b -> (xs :~: ys , a :~: b)
aligned a b =
  case decEq a b of
    Just Refl -> 
      case a =?= b of
        Just Refl -> (Refl, Refl)
        _ -> error $ "Scripts not aligned: " ++ string a ++ " <-> " ++ string b

--------------------------------------------------------------------------------
instance Show (ES3 xs) where
  show End3 = "End3"
  show (Ins3 x xs) = "Ins3 " ++ string x ++ " $ " ++ show xs
  show (Del3 x xs) = "Del3 " ++ string x ++ " $ " ++ show xs
  show (Upd3 x y xs) = "Upd3 " ++ string x ++ " " ++ string y ++ " $ " ++ show xs
  show (Cnf3 x xs) = "Cnf " ++ show x ++ " $ " ++ show xs

instance Show VConflict where
  show (InsIns a b) = "InsIns " ++ string a ++ " " ++ string b
  show (UpdDel a b) = "UpdDel " ++ string a ++ " " ++ string b
  show (DelUpd a b) = "DelUpd " ++ string a ++ " " ++ string b
  show (UpdUpd o a b) = "UpdUpd " ++ string o ++ " " ++ string a ++ " " ++ string b
