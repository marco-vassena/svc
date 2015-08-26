{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}

-- | This module provides a type-checker that transform a merged edit script
-- in a fully well-typed edit script, whose target object is the merged object.

module Data.DiffUtils.Diff3.TypeCheck where

import Data.TypeList.TList
import Data.DiffUtils.Diff hiding (IES)
import Data.DiffUtils.Diff3.Core
import Data.Typeable

-- | A simple wrapper for the type exected while type-checking.
newtype ExpectedType xs = ET (TList xs)

-- | Represents a type inferred in typeCheck
data InferredType xs where
  INil :: InferredType '[]
  ICons :: Typeable x => Proxy x -> InferredType xs -> InferredType (x ': xs)
  Top :: InferredType xs -- Can be anything, because of previous type errors

-- | Inferred type for an edit script
data IES xs where
  IES :: InferredType ys -> ES xs ys -> IES xs

-- | Well typed edit script
data WES xs where
  WES :: TList ys -> ES xs ys -> WES xs

-- | Represents a failure in the type-checker algorithm.
data TypeError where
  TyErr :: ExpectedType xs -> InferredType ys -> TypeError

-- | Converts an InferredType in TList. 
-- It fails with error if InferredType contains Top
toTList :: InferredType xs -> TList xs
toTList INil = TNil
toTList (ICons p i) = TCons p (toTList i)
toTList Top = error "toTList: InferredType contains Top"

-- | Convert a @TList@ in an @InferredType@.
toInferredType :: TList xs -> InferredType xs
toInferredType TNil = INil
toInferredType (TCons p t) = ICons p (toInferredType t)

--------------------------------------------------------------------------------

-- It represents the proof that two type unify.
data Unify a b where
  Same :: Unify a a
  Failed :: Unify a b -- a and b are different

-- The type @IsPrefixOf xs zs@ is the proof that the types xs are a prefix of zs,
-- according to some unifier, denoted by Unify.
data IsPrefixOf xs zs where
  Prefix :: InferredType ys -> Unify (xs :++: ys) zs -> IsPrefixOf xs zs

-- Checks whether a list is a prefix of the other
isPrefixOfTy :: TList as -> InferredType bs -> Maybe (IsPrefixOf as bs)
isPrefixOfTy TNil s = Just $ Prefix s Same
isPrefixOfTy s Top = Just $ Prefix Top Failed
isPrefixOfTy (TCons _ _) INil = Nothing
isPrefixOfTy (TCons x s1) (ICons y s2) =
  case (tyEq x y, isPrefixOfTy s1 s2) of
    (Just Refl, Just (Prefix s Same)) -> Just $ Prefix s Same
    (Just Refl, Just (Prefix s Failed)) -> Just $ Prefix s Failed -- TODO is it s or ICons x s
    _ -> Nothing

--------------------------------------------------------------------------------

-- This data-type includes the two kind of conflicts that
-- can be detected while merging.
-- The first constructor @VConf@ is about value related conflicts, 
-- i.e. two aligned incompatible edits have been made.
-- The second constructor @TConf@ denotes that a properly
-- merged edit cannot be included in the merged edit script,
-- because of a type-mismatch.
data Conflict = VConf (VConflict)
              | TConf (TypeError)
  deriving (Show)

-- | Typechecks a merged edit script and either returns
-- a well-typed edit script or a list of conflicts.
typeCheck ::  ES3 xs -> Either [Conflict] (WES xs)
typeCheck e = 
  case tyCheck e of
    ([]  , IES ty e') -> Right $ WES (toTList ty) e'
    (errs, _        ) -> Left errs

-- | Typechecks an edit script and collects all the type errors and value conflicts.
-- The script IES is fully defined only if no conflicts are reported.
tyCheck ::  ES3 xs -> ([Conflict], IES xs)
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
      case xs `isPrefixOfTy` ty of
        Just (Prefix xsys Same) -> (tyErr, IES (ICons Proxy xsys) (Ins x e'))
        Just (Prefix xsys Failed) -> (tyErr, IES (ICons Proxy xsys) (Ins x undefined))
        Nothing -> (TConf (TyErr (ET xs) ty) : tyErr, IES (ICons Proxy Top) (Ins x undefined))
tyCheck (Upd3 x y e) = 
  case tyCheck e of
    (tyErr, IES ty e') ->
      let ys = argsTy y in
      case ys `isPrefixOfTy` ty of
        Just (Prefix yszs Same) -> (tyErr, IES (ICons Proxy yszs) (Upd x y e'))
        Just (Prefix yszs Failed) -> (tyErr, IES (ICons Proxy yszs) (Upd x y undefined))
        Nothing -> (TConf (TyErr (ET ys) ty) : tyErr, IES (ICons Proxy Top) (Upd x y undefined))

--------------------------------------------------------------------------------

instance  Show TypeError where
  show (TyErr expected inferred) = "TyErr " ++ show expected ++ " " ++ show inferred 

instance  Show (InferredType xs) where
  show is = "[" ++ showIType is ++ "]"
 
showIType :: InferredType xs -> String
showIType INil = ""
showIType (ICons x INil) = showTy x 
showIType (ICons x is) = showTy x ++ ", " ++ showIType is
showIType Top = "Top"

instance Show (ExpectedType xs) where
  show (ET ts) = "[" ++ showTList ts ++ "]"

showTList :: TList xs -> String
showTList TNil = ""
showTList (TCons x TNil) = showTy x
showTList (TCons x ts) = showTy x ++ ", " ++ showTList ts
