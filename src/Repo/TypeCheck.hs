{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Repo.TypeCheck where

import Data.Type.Equality
import Data.Proxy
import Data.TypeList.SList
import Data.TypeList.DList
import Repo.Diff
import Repo.Diff3

-- TODO Inferred type instead of Well-Typed
-- Well-typed edit script
data WES f xs where
  WES :: TList f ys -> ES f xs ys -> WES f xs

-- Represents a failure in the type-checker algorithm.
data TypeError f where
  -- TODO include slice of ES3 ?
  TyErr :: ExpectedType f xs -> InferredType f ys -> TypeError f

-- A simple wrapper for the type exected while type-checking.
newtype ExpectedType f xs = ET (TList f xs)

-- The type @IsPrefixOf f xs zs@ is the proof that the types xs are a prefix of zs,
-- according to some unifier, denoted by Unify.
data IsPrefixOf f xs zs where
  Prefix :: TList f ys -> (xs :++: ys) :~: zs -> IsPrefixOf f xs zs

-- Checks whether a list is a prefix of the other
isTyPrefixOf :: Family f => TList f as -> TList f bs -> Maybe (IsPrefixOf f as bs)
isTyPrefixOf TNil s = Just $ Prefix s Refl
isTyPrefixOf (TCons _ _) TNil = Nothing
isTyPrefixOf (TCons x s1) (TCons y s2) =
  case (isTyPrefixOf s1 s2, tyEq (proxyOfTL s1) x y) of
    (Just (Prefix s Refl), Just Refl) -> Just $ Prefix s Refl
    _ -> Nothing

--------------------------------------------------------------------------------
-- TODO remark in thesis: is it possible to catch multiple type errors in this setting?
--data Unify a b where
--  Same :: Unify a a
--  TyErr :: Unify a b -- a and b are different

-- Prefix would report TyErr whenever a or b comes from Top

-- Use type check and report left if there is at least one error.
typeCheck :: Family f => ES3 f xs -> Either [TypeError f] (WES f xs)
typeCheck = undefined

-- instead of FList we need some form of reified type,
-- which includes type error, that can be unified with everything.
data InferredType f xs where
  INil :: InferredType f '[]
  ICons :: (x :<: f) => Proxy x -> InferredType f xs -> InferredType f (x ': xs)
  Top :: InferredType f xs -- Can be anything, because of previous type errors

-- TODO multiple type error report?
-- Exploiting laziness, we can pair a WES with type error.
-- WES is fully defined only if no errors are reported.
tyCheck :: Family f => ES3 f xs -> Either (TypeError f) (WES f xs)
tyCheck End3 = Right $ WES TNil End
tyCheck (Cnf3 c _) = error $  "Conflict detected: " ++ show c
tyCheck (Del3 x e) = 
  case tyCheck e of
    Right (WES ty e') -> Right $ WES ty (Del x e')
    Left tyErr -> Left tyErr
tyCheck (Ins3 x e) = 
  case tyCheck e of
    Right (WES ty e') -> 
      let xs = argsTy x in
      case xs `isTyPrefixOf` ty of
        Just (Prefix xsys Refl) -> Right $ WES (TCons Proxy xsys) (Ins x e')
        Nothing -> Left $ TyErr (ET xs) undefined
    Left tyErr -> Left tyErr
tyCheck (Upd3 x y e) = 
  case tyCheck e of
    Right (WES ty e') ->
      let ys = argsTy y in
      case ys `isTyPrefixOf` ty of
        Just (Prefix yszs Refl) -> Right $ WES (TCons Proxy yszs) (Upd x y e')
        Nothing -> Left $ TyErr (ET ys) undefined
    Left tyErr -> Left tyErr
