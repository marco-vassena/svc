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
import Data.Type.Equality
import Repo.Diff

-- An edit script @ES3 f xs ys zs@ represents is an edit scripts
-- that represents changes from @xs@ to @ys@ and from @xs@ to @zs@.
data ES3 f xs ys where
  -- | Inserts something new in the tree
  Ins3 :: (a :<: f) => f xs a -> ES3 f ys (xs :++: zs) -> ES3 f ys (a ': zs)
  -- | Removes something from the original tree
  Del3 :: (a :<: f) => f xs a -> ES3 f (xs :++: ys) zs -> ES3 f (a ': ys) zs  
  -- | Replaces something in the original tree
  Upd3 :: (a :<: f) => f xs a -> f ys a -> ES3 f (xs :++: zs) (ys :++: ws) -> ES3 f (a ': zs) (a ': ws)
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

  -- Type-related conflicts
  BadIns :: f xs a -> Conflict f
  CpyDel :: f xs a -> Conflict f
  CpyUpd :: f xs a -> f ys a -> Conflict f

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

instance Reify (FList f) where
  toSList FNil = SNil
  toSList (FCons _ fs) = SCons (toSList fs)

fTake :: SList xs -> g ys -> FList f (xs :++: ys) -> FList f xs
fTake SNil _ _ = FNil
fTake (SCons s1) s2 (FCons x xs) = FCons x (fTake s1 s2 xs)

fTail :: FList f (a ': xs) -> FList f xs
fTail (FCons _ xs) = xs

-- TODO refactoring
-- Merges two ES scripts in an ES3 script.
diff3 :: (Family f, Metric f) => ES f xs ys -> ES f xs zs -> ES3 f xs ys
diff3 a@(Upd o x xs) b@(Upd o' y ys) = 
  case aligned o o' of
    (Refl, Refl) -> 
      case (o =?= x, o' =?= y, x =?= y) of
          (Just (Refl, Refl), _, _) -> 
              case (collect2 a, collect2 b) of
                (FCons _ fxs, FCons _ fys) -> 
                  case eq fxs fys of
                    Just Refl -> Upd3 o y (diff3 ys xs)  -- Swap
                    Nothing -> 
                      let fas = fTake (reifyF x) fxs (collect2 xs)
                          fbs = fTake (reifyF y) fys (collect2 ys) in
                        case eq fas fbs of
                          Just Refl -> Upd3 o y (diff3 xs ys)  -- No Swap
                          Nothing -> Cnf3 (CpyUpd x y) (diff3 xs ys)
          (_, Just (Refl, Refl), _) -> Upd3 o x (diff3 xs ys)
          (_, _, Just (Refl, Refl)) -> Upd3 o x (diff3 xs ys) -- False positive, the scripts agree
          (_, _, _                ) -> Cnf3 (UpdUpd x y) (diff3 xs ys)
diff3 a@(Upd o x xs) (Del o' ys) =
  case aligned o o' of
    (Refl, Refl) -> 
      case o =?= x of
        Just (Refl, Refl) -> 
          let fa = collect2 a
              fb = collect2 ys in
            case eq fa fb of
              Just Refl -> Del3 o (diff3 ys xs)  -- Swap
              Nothing -> 
                let fxs = fTake (reifyF x) (fTail fa) (collect2 xs) in 
                  case eq fxs (FCons x FNil) of
                    Just Refl -> Del3 o (diff3 xs ys) -- No Swap
                    Nothing -> Cnf3 (CpyDel o) (diff3 xs ys)
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
diff3 e1 e2@(Ins y ys) = 
  let f2 = collect2 e2
      f1 = collect2 e1 in
  case eq f1 f2 of
    Just Refl -> Ins3 y (diff3 ys e1)
    Nothing   -> Cnf3 (BadIns y) (diff3 e1 ys)
diff3 End End = End3

-- Checks whether the two witnesses are the same,
-- and fails if this is not the case.
aligned :: Family f => f xs a -> f ys b -> (xs :~: ys , a :~: b)
aligned a b =
  case a =?= b of
    Just (Refl, Refl) -> (Refl, Refl)
    _ -> error $ "Scripts not aligned: " ++ string a ++ " <-> " ++ string b

--------------------------------------------------------------------------------
-- Auxiliary functions and data-types used in the diff3 algorithm
--------------------------------------------------------------------------------

eq :: Family f => FList f xs -> FList f ys -> Maybe (xs :~: ys)
eq FNil FNil = Just Refl
eq (FCons _ _) FNil = Nothing
eq FNil (FCons _ _) = Nothing
eq (FCons x xs) (FCons y ys) = 
  case (decEq x y, eq xs ys) of
    (Just Refl, Just Refl) -> Just Refl
    _ -> Nothing

data FList f xs where
  FNil :: FList f '[]
  FCons :: f as a -> FList f xs -> FList f (a ': xs)

fdrop :: SList xs -> FList f (xs :++: ys) -> FList f ys
fdrop SNil fs = fs
fdrop (SCons s) (FCons _ fs) = fdrop s fs

collect1 :: Family f => ES f xs ys -> FList f xs
collect1 End = FNil
collect1 (Ins x e) = collect1 e
collect1 (Del x e) = FCons x fs
  where fs = fdrop (reifyF x) (collect1 e)
collect1 (Upd x y e) = FCons x fs
  where fs = fdrop (reifyF x) (collect1 e)

collect2 :: Family f => ES f xs ys -> FList f ys
collect2 End = FNil
collect2 (Ins x e) = FCons x fs
  where fs = fdrop (reifyF x) (collect2 e)
collect2 (Del x e) = collect2 e
collect2 (Upd x y e) = FCons y fs
  where fs = fdrop (reifyF y) (collect2 e)

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
