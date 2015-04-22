{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Expr where

import Repo.Diff3 hiding (Add)
import Data.Type.Equality hiding (apply)

data Expr = Add Expr Expr
          | Times Expr Expr
          | If Expr Expr Expr
          | BVal Bool
          | IVal Int
  deriving (Show, Eq)

e0 :: Expr
e0 = Add (IVal 1) (IVal 2)

e1 :: Expr
e1 = Times e0 (IVal 3)

e2 :: Expr
e2 = If (BVal True) e0 e1

t0, t1, t2 :: DTree ExprF Expr
t0 = toTree e0
t1 = toTree e1
t2 = toTree e2

--------------------------------------------------------------------------------
-- With singleton types (like GDiff)

data ExprF xs a where
  Add''   :: ExprF [Expr,Expr] Expr
  Times'' :: ExprF [Expr,Expr] Expr
  If''    :: ExprF [Expr, Expr,Expr] Expr
  IVal''  :: ExprF '[Int] Expr
  BVal''  :: ExprF '[Bool] Expr
  Bool''  :: Bool -> ExprF '[] Bool
  Int''   :: Int -> ExprF '[] Int

instance TreeLike ExprF Expr where
  toTree (Add e1 e2) = Node Add'' args
    where args = DCons (toTree e1) $ DCons (toTree e2) DNil
  toTree (Times e1 e2) = Node Times'' args
    where args = DCons (toTree e1) $ DCons (toTree e2) DNil
  toTree (If e1 e2 e3) = Node If'' args
    where args = DCons (toTree e1) $ DCons (toTree e2) $ DCons (toTree e3) $ DNil
  toTree (IVal i) = Node IVal'' $ DCons t DNil
    where t = Node (Int'' i) DNil
  toTree (BVal b) = Node BVal'' $ DCons t DNil
    where t = Node (Bool'' b) DNil

  fromTree (Node c cs) = apply c cs

instance TreeLike ExprF Int where
  toTree i = Node (Int'' i) DNil -- Not so sure this makes sense
  fromTree (Node f DNil) = apply f DNil

instance TreeLike ExprF Bool where
  toTree b = Node (Bool'' b) DNil
  fromTree (Node f DNil) = apply f DNil

instance Family ExprF where
  apply Add'' (DCons e1 (DCons e2 DNil)) = Add (fromTree e1) (fromTree e2)
  apply Times'' (DCons e1 (DCons e2 DNil)) = Times (fromTree e1) (fromTree e2)
  apply If'' (DCons e0 (DCons e1 (DCons e2 DNil))) = If (fromTree e0) (fromTree e1) (fromTree e2) 
  apply IVal'' (DCons i DNil) = IVal (fromTree i)
  apply BVal'' (DCons b DNil) = BVal (fromTree b)
  apply (Int'' i) DNil = i
  apply (Bool'' b) DNil = b
  
  string Add'' = "Add"
  string (Int'' i) = show i
  string (Bool'' b) = show b
  string IVal'' = "IVal"
  string BVal'' = "BVal"
  string If''   = "If"
  string Times'' = "Times"

  decEq (Int'' _) (Int'' _) = Just Refl
  decEq (Bool'' _) (Bool'' _) = Just Refl  -- TODO here the type is the same but we need to cmp the values
  decEq IVal'' IVal'' = Just Refl
  decEq Times'' Times'' = Just Refl
  decEq Add'' Add'' = Just Refl
  decEq If'' If'' = Just Refl
  decEq _    _    = Nothing

instance Metric ExprF where
  distance (Int'' x) (Int'' y) = if x == y then 0 else 1
  distance (Bool'' x) (Bool'' y) = if x == y then 0 else 1
  distance If'' If'' = 0
  distance Times'' Times'' = 0
  distance Add'' Add'' = 0
  distance BVal'' BVal'' = 0
  distance IVal'' IVal'' = 0
  distance _ _ = 1 -- Here we could defined more fine-grained distances

