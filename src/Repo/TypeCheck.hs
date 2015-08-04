{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module Repo.TypeCheck where

import Data.Type.Equality
import Data.Proxy
import Data.TypeList.SList
import Data.TypeList.DList
import Repo.Diff hiding (IES)
import Repo.Diff3

-- A simple wrapper for the type exected while type-checking.
newtype ExpectedType f xs = ET (TList f xs)

-- Represents a type inferred in typeCheck
data InferredType f xs where
  INil :: InferredType f '[]
  ICons :: (x :<: f) => Proxy x -> InferredType f xs -> InferredType f (x ': xs)
  Top :: InferredType f xs -- Can be anything, because of previous type errors

-- Inferred type for an edit script
data IES f xs where
  IES :: InferredType f ys -> ES f xs ys -> IES f xs

-- Well typed edit script
data WES f xs where
  WES :: TList f ys -> ES f xs ys -> WES f xs

-- Represents a failure in the type-checker algorithm.
data TypeError f where
  -- TODO include slice of ES3 ?
  TyErr :: ExpectedType f xs -> InferredType f ys -> TypeError f

-- Converts an InferredType in TList. 
-- It fails with error if InferredType contains Top
toTList :: InferredType f xs -> TList f xs
toTList INil = TNil
toTList (ICons p i) = TCons p (toTList i)
toTList Top = error "toTList: InferredType contains Top"

--------------------------------------------------------------------------------
data Unify a b where
  Same :: Unify a a
  Failed :: Unify a b -- a and b are different

-- The type @IsPrefixOf f xs zs@ is the proof that the types xs are a prefix of zs,
-- according to some unifier, denoted by Unify.
data IsPrefixOf f xs zs where
  Prefix :: InferredType f ys -> Unify (xs :++: ys) zs -> IsPrefixOf f xs zs

-- Checks whether a list is a prefix of the other
isTyPrefixOf :: Family f => TList f as -> InferredType f bs -> Maybe (IsPrefixOf f as bs)
isTyPrefixOf TNil s = Just $ Prefix s Same
isTyPrefixOf s Top = Just $ Prefix Top Failed
isTyPrefixOf (TCons _ _) INil = Nothing
isTyPrefixOf (TCons x s1) (ICons y s2) =
  case (isTyPrefixOf s1 s2, tyEq (proxyOfTL s1) x y) of
    (Just (Prefix s Same), Just Refl) -> Just $ Prefix s Same
    _ -> Nothing

--------------------------------------------------------------------------------
-- Prefix would report TyErr whenever a or b comes from Top

-- Use type check and report left if there is at least one error.
typeCheck :: Family f => ES3 f xs -> Either [TypeError f] (WES f xs)
typeCheck e = 
  case tyCheck e of
    ([]  , IES ty e') -> Right $ WES (toTList ty) e'
    (errs, _        ) -> Left $ errs

-- TODO multiple type error report?
-- Exploiting laziness, we can pair a IES with type error.
-- IES is fully defined only if no errors are reported.
tyCheck :: Family f => ES3 f xs -> ([TypeError f], IES f xs)
tyCheck End3 = ([], IES INil End)
tyCheck (Cnf3 c e) = error $ "Conflict detected: " ++ show c
tyCheck (Del3 x e) = 
  case tyCheck e of
    (tyErr, IES ty e') -> (tyErr, IES ty (Del x e'))
tyCheck (Ins3 x e) = 
  case tyCheck e of
    (tyErr, IES ty e') -> 
      let xs = argsTy x in
      case xs `isTyPrefixOf` ty of
        Just (Prefix xsys Same) -> (tyErr, IES (ICons Proxy xsys) (Ins x e'))
        -- TODO better error message
        -- TODO return part of the edit script, or just undefined?
        Just (Prefix xsys Failed) -> (tyErr, IES (ICons Proxy xsys) (Ins x undefined))
        Nothing -> (TyErr (ET xs) ty : tyErr, IES (ICons Proxy Top) (Ins x undefined))
tyCheck (Upd3 x y e) = 
  case tyCheck e of
    (tyErr, IES ty e') ->
      let ys = argsTy y in
      case ys `isTyPrefixOf` ty of
        Just (Prefix yszs Same) -> (tyErr, IES (ICons Proxy yszs) (Upd x y e'))
        -- TODO better error message
        -- TODO return part of the edit script, or just undefined?
        Just (Prefix yszs Failed) -> (tyErr, IES (ICons Proxy yszs) (Upd x y undefined))
        Nothing -> (TyErr (ET ys) ty : tyErr, IES (ICons Proxy Top) (Upd x y undefined))
