{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

module Data.DiffUtils.Diff3.TypeCheck where

import Data.Type.Equality
import Data.Proxy
import Data.TypeList.SList
import Data.TypeList.DList
import Data.DiffUtils.Diff hiding (IES)
import Data.DiffUtils.Diff3.Core

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

toInferredType :: TList f xs -> InferredType f xs
toInferredType TNil = INil
toInferredType (TCons p t) = ICons p (toInferredType t)

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
  case (tyEq (proxyOfTL s1) x y, isTyPrefixOf s1 s2) of
    (Just Refl, Just (Prefix s Same)) -> Just $ Prefix s Same
    _ -> Nothing

--------------------------------------------------------------------------------

-- This data-type includes the two kind of conflicts that
-- can be detected while merging.
-- The first constructor @VConf@ is about value related conflicts, 
-- i.e. two aligned incompatible edits have been made.
-- The second constructor @TConf@ denotes that a properly
-- merged edit cannot be included in the merged edit script,
-- because of a type-mismatch.
data Conflict f = VConf (VConflict f)
                | TConf (TypeError f)
  deriving (Show)

-- Use type check and report left if there is at least one error.
typeCheck :: Family f => ES3 f xs -> Either [Conflict f] (WES f xs)
typeCheck e = 
  case tyCheck e of
    ([]  , IES ty e') -> Right $ WES (toTList ty) e'
    (errs, _        ) -> Left $ errs

-- Exploiting laziness, we can pair a IES with type error.
-- The script IES is fully defined only if no errors are reported.
tyCheck :: Family f => ES3 f xs -> ([Conflict f], IES f xs)
tyCheck End3 = ([], IES INil End)
tyCheck (Cnf3 c e) = 
  case tyCheck e of 
    (tyErr, IES ty e') -> (VConf c : tyErr, IES Top undefined)
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
        Nothing -> (TConf (TyErr (ET xs) ty) : tyErr, IES (ICons Proxy Top) (Ins x undefined))
tyCheck (Upd3 x y e) = 
  case tyCheck e of
    (tyErr, IES ty e') ->
      let ys = argsTy y in
      case ys `isTyPrefixOf` ty of
        Just (Prefix yszs Same) -> (tyErr, IES (ICons Proxy yszs) (Upd x y e'))
        -- TODO better error message
        -- TODO return part of the edit script, or just undefined?
        Just (Prefix yszs Failed) -> (tyErr, IES (ICons Proxy yszs) (Upd x y undefined))
        Nothing -> (TConf (TyErr (ET ys) ty) : tyErr, IES (ICons Proxy Top) (Upd x y undefined))

--------------------------------------------------------------------------------

instance Family f => Show (TypeError f) where
  show (TyErr expected inferred) = "TyErr " ++ show expected ++ " " ++ show inferred 

instance Family f => Show (InferredType f xs) where
  show is = "[" ++ showIType is Proxy ++ "]"
 
showIType :: Family f => InferredType f xs -> Proxy f -> String
showIType INil _ = ""
showIType (ICons x INil) p = stringOfTy x p
showIType (ICons x is) p = stringOfTy x p ++ ", " ++ showIType is p
showIType Top _ = "Top"

instance Family f => Show (ExpectedType f xs) where
  show (ET ts) = "[" ++ showTList ts Proxy ++ "]"

showTList :: Family f => TList f xs -> Proxy f -> String
showTList TNil _ = ""
showTList (TCons x TNil) p = stringOfTy x p
showTList (TCons x ts) p = stringOfTy x p ++ ", " ++ showTList ts p
