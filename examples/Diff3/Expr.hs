{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Expr where

import Data.Typeable
import Data.TypeList.HList
import Data.DiffUtils
import Data.Type.Equality

data Expr = Add Expr Expr
          | Times Expr Expr
          | If Expr Expr Expr
          | BVal Bool
          | IVal Int
  deriving (Show, Eq, Typeable)

e0 :: Expr
e0 = Add (IVal 1) (IVal 2)

e1 :: Expr
e1 = Times (IVal 1) (IVal 3)

e2 :: Expr
e2 = If (IVal 1) (Add (IVal 2) (IVal 3)) (BVal False)

e3 :: Expr
e3 = Add (IVal 1) (IVal 2)

e4 = If (IVal 1) (IVal 2) (IVal 3)
--------------------------------------------------------------------------------
-- Diff
--------------------------------------------------------------------------------

d01, d02, d03 :: ES '[Expr] '[Expr]
d01 = gdiff e0 e1
d02 = gdiff e0 e2 
d03 = gdiff e0 e3
d23 = gdiff e2 e3
d24 = gdiff e2 e4

--------------------------------------------------------------------------------
-- Diff3
--------------------------------------------------------------------------------

e102 :: Either [Conflict] Expr
e102 = diff3Patch e1 e0 e2

e203 :: Either [Conflict] Expr
e203 = diff3Patch e2 e0 e3

e124 :: Either [Conflict] Expr
e124 = diff3Patch e1 e2 e4

--------------------------------------------------------------------------------

data BoolF xs x where
  True' :: BoolF '[] Bool
  False' :: BoolF '[] Bool

data ExprF xs x where
  Add' :: ExprF '[Expr, Expr] Expr
  Times' :: ExprF '[Expr, Expr] Expr
  If' :: ExprF '[Expr, Expr, Expr] Expr
  BVal' :: ExprF '[Bool] Expr
  IVal' :: Int -> ExprF '[] Expr

instance Diff Expr where
  type FamilyOf Expr = ExprF
  
  string Add'      = "Add"
  string Times'     = "Time"
  string If'       = "If"
  string BVal'     = "BVal"
  string (IVal' _) = "IVal"

  argsTy Add'      = tlist
  argsTy Times'     = tlist
  argsTy If'       = tlist
  argsTy BVal'     = tlist
  argsTy (IVal' _) = tlist
 
  Add'      =?= Add'      = Just Refl
  Times'    =?= Times'     = Just Refl  
  If'       =?= If'       = Just Refl  
  BVal'     =?= BVal'     = Just Refl  
  (IVal' x) =?= (IVal' y) = if x == y then Just Refl else Nothing
  _         =?= _         = Nothing

  -- Just to avoid some boilerplate code ...
  distance x y = maybe 1 (const 0) (x =?= y) 

  fromDTree (Node Add' (DCons x (DCons y DNil))) 
    = Add (fromDTree x) (fromDTree y)
  fromDTree (Node Times' (DCons x (DCons y DNil))) 
    = Times (fromDTree x) (fromDTree y)   
  fromDTree (Node If' (DCons c (DCons x (DCons y DNil)))) 
    = If (fromDTree c) (fromDTree x) (fromDTree y)   
  fromDTree (Node BVal' (DCons x DNil)) = BVal (fromDTree x) 
  fromDTree (Node (IVal' x) DNil) = IVal x

  toDTree (Add x y) = Node Add' $ DCons (toDTree x) (DCons (toDTree y) DNil)
  toDTree (Times x y) = Node Times' $ DCons (toDTree x) (DCons (toDTree y) DNil)
  toDTree (If c x y) = Node If' $ DCons (toDTree c) $ DCons (toDTree x) $ DCons (toDTree y) DNil
  toDTree (BVal e) = Node BVal' $ DCons (toDTree e) DNil
  toDTree (IVal x) = Node (IVal' x) DNil

instance Diff Bool where
  type FamilyOf Bool = BoolF

  string True' = "True"
  string False' = "False"

  True'  =?= True'  = Just Refl
  False' =?= False' = Just Refl
  _      =?= _      = Nothing

  distance x y = maybe 1 (const 0) (x =?= y) 

  fromDTree (Node True' DNil) = True
  fromDTree (Node False' DNil) = False
  
  toDTree True = Node True' DNil
  toDTree False = Node False' DNil

  argsTy True' = tlist
  argsTy False' = tlist
