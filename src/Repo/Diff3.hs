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
import Data.HList (Append)
import Data.Type.Equality
import Repo.Diff

-- An edit script @ES3 f xs ys zs@ represents is an edit scripts
-- that represents changes from @xs@ to @ys@ and from @xs@ to @zs@.
data ES3 f xs ys where
  -- | Inserts something new in the tree
  Ins3 :: (a :<: f, KnownSList f xs) => f xs a -> ES3 f ys (xs :++: zs) -> ES3 f ys (a ': zs)
  -- | Removes something from the original tree
  Del3 :: (a :<: f, KnownSList f xs) => f xs a -> ES3 f (xs :++: ys) zs -> ES3 f (a ': ys) zs  
  -- | Replaces something in the original tree
  Upd3 :: (a :<: f, KnownSList f xs, KnownSList f ys) => f xs a -> f ys a -> ES3 f (xs :++: zs) (ys :++: ws) -> ES3 f (a ': zs) (a ': ws)
  -- | A conflict between the two edit script
  Cnf3 :: Conflict f -> ES3 f xs ys -> ES3 f zs ws
  -- | Terminates the edit script
  End3 :: ES3 f '[] '[]

-- Represents what kind of conflict has been detected.
data Conflict f where
  InsIns :: f xs a -> f ys b -> Conflict f
  UpdDel :: f xs a -> f ys b -> Conflict f
  DelUpd :: f xs a -> f ys b -> Conflict f
  UpdUpd :: f xs a -> f ys b -> Conflict f

-- Applies the edit script to the original object merging changes in different versions
-- of the object. It fails if the script contains a conflict.
patch3 :: (Family f, Metric f) => Proxy f -> ES3 f xs ys -> DList f xs -> DList f ys
patch3 p (Upd3 x y e)  = insert y . patch3 p e . delete p x 
patch3 p (Del3 x e)    =            patch3 p e . delete p x 
patch3 p (Ins3 x e)    = insert x . patch3 p e
patch3 p (Cnf3 c e)    = error $ "patch3: Conflict detected " ++ show c
patch3 _ End3          = id 

-- Collects the conflict that may be present in the edit script.
getConflicts :: ES3 f xs ys -> [Conflict f]
getConflicts (Upd3 _ _ e) = getConflicts e
getConflicts (Ins3 _ e) = getConflicts e
getConflicts (Del3 _ e) = getConflicts e
getConflicts (Cnf3 c e) = c : getConflicts e
getConflicts End3 = []

-- We can update a value, when the other is copied, 
-- only if they have the same fields.
agreeCpyUpd :: f xs a -> f ys a -> Maybe (xs :~: ys)
agreeCpyUpd = undefined

-- Merges two ES scripts in an ES3 script.
diff3 :: (Family f, Metric f) => ES f xs ys -> ES f xs zs -> ES3 f xs ys
diff3 (Upd o x xs) (Upd o' y ys) = 
  case aligned o o' of
    (Refl, Refl) -> 
      case (o =?= x, o' =?= y, x =?= y) of
          (Just (Refl, Refl), _, _) -> 
            case agreeCpyUpd x y of
              Just Refl -> Upd3 o y (diff3 xs ys)
              Nothing -> Cnf3 (UpdUpd x y) (diff3 xs ys)
          (_, Just (Refl, Refl), _) -> Upd3 o x (diff3 xs ys)
          (_, _, Just (Refl, Refl)) -> Upd3 o x (diff3 xs ys) -- False positive, the scripts agree
          (_, _, _                ) -> Cnf3 (UpdUpd x y) (diff3 xs ys)
diff3 (Upd o x xs) (Del o' ys) =
  case aligned o o' of
    (Refl, Refl) -> 
      case o =?= x of
        Just (Refl, Refl) -> Del3 o undefined -- (diff ys zs)
--          let (xs', yws') = toSList2 xs
--              ws' = sSplit undefined yws'
--              (_, zs') = toSList2 ys in undefined
--           case agreeDelCpy1 o undefined undefined undefined xs ys of
--              Just Refl -> undefined -- Del3 o (diff3 ys xs)
--              Nothing -> Cnf3 (DelUpd x o) (diff3 xs ys)
        _ -> Cnf3 (UpdDel x o) (diff3 xs ys)
diff3 (Del o xs) (Upd o' y ys) =
  case aligned o o' of
    (Refl, Refl) -> 
      case o' =?= y of
        Just (Refl, Refl) -> Del3 o (diff3 xs ys)
        _ -> Cnf3 (DelUpd o y) (diff3 xs ys)
diff3 (Del x xs) (Del y ys) =
  case aligned x y of
    (Refl, Refl) -> Del3 x (diff3 xs ys)
diff3 (Ins x xs) (Ins y ys) = 
  case x =?= y of
    Just (Refl, Refl) -> Ins3 x (diff3 xs ys)
    _ -> Cnf3 (InsIns x y) (diff3 xs ys)
diff3 (Ins x xs) ys = Ins3 x (diff3 xs ys) 
diff3 xs (Ins y ys) = undefined
diff3 End End = End3

-- Checks whether the two witnesses are the same,
-- and fails if this is not the case.
aligned :: Family f => f xs a -> f ys b -> (xs :~: ys , a :~: b)
aligned a b =
  case a =?= b of
    Just (Refl, Refl) -> (Refl, Refl)
    _ -> error $ "Scripts not aligned: " ++ string a ++ " <-> " ++ string b

--------------------------------------------------------------------------------
instance Family f => Show (ES3 f xs ys) where
  show End3 = "End3"
  show (Ins3 x xs) = "Ins3 " ++ string x ++ " $ " ++ show xs
  show (Del3 x xs) = "Del3 " ++ string x ++ " $ " ++ show xs
  show (Upd3 x y xs) = "Upd3 " ++ string x ++ " " ++ string y ++ " $ " ++ show xs
  show (Cnf3 x xs) = "Cnf " ++ show x ++ " $ " ++ show xs

instance Family f => Show (Conflict f) where
  show (InsIns a b) = "InsIns " ++ string a ++ " " ++ string b
  show (UpdDel a b) = "UpdDel " ++ string a ++ " " ++ string b
  show (DelUpd a b) = "DelUpd " ++ string a ++ " " ++ string b
  show (UpdUpd a b) = "UpdUpd " ++ string a ++ " " ++ string b
