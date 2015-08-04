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

-- An edit script @ES3 f xs@ represents a merged edit script.
-- It is well-typed with respect to the source object, but
-- it may be ill-typed with respect to the source object,
-- or it might contain value-related conflicts.
data ES3 f xs where
  -- | Inserts something new in the tree
  Ins3 :: (a :<: f) => f xs a -> ES3 f ys -> ES3 f ys
  -- | Removes something from the original tree
  Del3 :: (a :<: f) => f xs a -> ES3 f (xs :++: ys) -> ES3 f (a ': ys)
  -- | Replaces something in the original tree
  Upd3 :: (a :<: f) => f xs a -> f ys a -> ES3 f (xs :++: zs) -> ES3 f (a ': zs)
  -- | A conflict between the two edit script
  Cnf3 :: Conflict f -> ES3 f xs -> ES3 f ys -- TODO remark that it is not worth to make this case well-typed
  -- | Terminates the edit script
  End3 :: ES3 f '[]

--------------------------------------------------------------------------------
-- TODO point out problems with ambiguity when trying to decouple ES from single edits.
--data Edit f as bs cs ds where
--  EIns :: f as a -> Edit f '[] '[] as '[ a ]
--  EDel :: f as a -> Edit f as '[ a ] '[] '[]
--  EUpd :: f as a -> f bs a -> Edit f as '[ a ] bs '[ a ]
--
-- A list of edit scripts, either well-typed or with typed-errors 
--data Edits f xs ys where
--  ENil :: Edits f '[] '[]
--  ECons :: SList xs -> SList ys -> Edit f as bs cs ds 
--        -> Edits f (as :++: xs) (cs :++: ys) -> Edits f (bs :++: xs) (ds :++: ys)
--  ETyErr :: Edit f as bs cs ds -> Edits f xs ys -> Edits f zs ws
-------------------------------------------------------------------------------- 

-- Represents what kind of conflict has been detected.
data Conflict f where
  InsIns :: f xs a -> f ys b -> Conflict f
  UpdDel :: f xs a -> f ys a -> Conflict f
  DelUpd :: f xs a -> f ys a -> Conflict f
  UpdUpd :: f xs a -> f ys a -> f zs a -> Conflict f

-- Collects the conflict that may be present in the edit script.
getConflicts :: ES3 f xs -> [Conflict f]
getConflicts (Upd3 _ _ e) = getConflicts e
getConflicts (Ins3 _ e) = getConflicts e
getConflicts (Del3 _ e) = getConflicts e
getConflicts (Cnf3 c e) = c : getConflicts e
getConflicts End3 = []

--------------------------------------------------------------------------------

-- User friendly entry point
-- TODO: Provide user-friendly entry point, i.e. checks for expected type.
-- TODO maybe even more friendly expecting directly raw types instead of DList ?
-- TODO Safer interface: errors for types or conflicts.
diff3 :: DList f ys -> DList f xs -> DList f ys -> ES f xs ys
diff3 = undefined

-- Merges two ES scripts in an ES3 script.
merge3 :: (Family f, Metric f) => ES f xs ys -> ES f xs zs -> ES3 f xs
merge3 a@(Upd o x xs) b@(Upd o' y ys) = 
  case aligned o o' of
    (Refl, Refl) -> 
      case (o =?= x, o' =?= y, x =?= y) of
        (Just (Refl, Refl), _, _) -> Upd3 o y (merge3 xs ys) -- Id1
        (_, Just (Refl, Refl), _) -> Upd3 o x (merge3 xs ys) -- Id2
        (_, _, Just (Refl, Refl)) -> Upd3 o x (merge3 xs ys) -- Idem
        (_, _, _                ) -> Cnf3 (UpdUpd o x y) (merge3 xs ys)
merge3 a@(Upd o x xs) (Del o' ys) =
  case aligned o o' of
    (Refl, Refl) -> 
      case o =?= x of
        Just (Refl, Refl) -> Del3 o (merge3 xs ys) -- Id1
        Nothing           -> Cnf3 (UpdDel o x) (merge3 xs ys)
merge3 (Del o xs) (Upd o' y ys) = 
  case aligned o o' of
    (Refl, Refl) -> 
      case o' =?= y of
        Just (Refl, Refl) -> Del3 o (merge3 xs ys) -- Id2
        Nothing           -> Cnf3 (DelUpd o y) (merge3 xs ys)
merge3 (Del x xs) (Del y ys) =
  case aligned x y of
    (Refl, Refl) -> Del3 x (merge3 xs ys) -- Idem
merge3 (Ins x xs) (Ins y ys) =
  case x =?= y of
    Just (Refl, Refl) -> Ins3 x (merge3 xs ys) -- Idem
    Nothing           -> Cnf3 (InsIns x y) (merge3 xs ys)
merge3 (Ins x xs) ys = Ins3 x (merge3 xs ys) -- Id2
merge3 xs (Ins y ys) = Ins3 y (merge3 xs ys) -- Id1
merge3 End End = End3

-- Checks whether the two witnesses are the same,
-- and fails if this is not the case.
aligned :: Family f => f xs a -> f ys b -> (xs :~: ys , a :~: b)
aligned a b =
  case a =?= b of
    Just (Refl, Refl) -> (Refl, Refl)
    _ -> error $ "Scripts not aligned: " ++ string a ++ " <-> " ++ string b

--------------------------------------------------------------------------------
instance Family f => Show (ES3 f xs) where
  show End3 = "End3"
  show (Ins3 x xs) = "Ins3 " ++ string x ++ " $ " ++ show xs
  show (Del3 x xs) = "Del3 " ++ string x ++ " $ " ++ show xs
  show (Upd3 x y xs) = "Upd3 " ++ string x ++ " " ++ string y ++ " $ " ++ show xs
  show (Cnf3 x xs) = "Cnf " ++ show x ++ " $ " ++ show xs

instance Family f => Show (Conflict f) where
  show (InsIns a b) = "InsIns " ++ string a ++ " " ++ string b
  show (UpdDel a b) = "UpdDel " ++ string a ++ " " ++ string b
  show (DelUpd a b) = "DelUpd " ++ string a ++ " " ++ string b
  show (UpdUpd o a b) = "UpdUpd " ++ string o ++ " " ++ string a ++ " " ++ string b
