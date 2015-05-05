{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Expr where

import Data.HList
import Data.Proxy -- TODO remove
import Repo.Diff3 hiding (Add)
import Data.Type.Equality hiding (build)

data Expr = Add Expr Expr
          | Times Expr Expr
          | If Expr Expr Expr
          | BVal Bool
          | IVal Int
  deriving (Show, Eq)

e0 :: Expr
e0 = Add (IVal 1) (IVal 2)

e1 :: Expr
e1 = Times (IVal 1) (IVal 3)

e2 :: Expr
e2 = If (IVal 1) (Add (IVal 2) (IVal 3)) (BVal False)

d01, d02 :: ES ExprF '[Expr] '[Expr]
d01 = gdiff e0 e1
d02 = gdiff e0 e2 

e1' :: Expr
e1' = case patch Proxy d01 (DCons e0 DNil) of
        DCons x DNil -> x

e2PatchFail :: Expr
e2PatchFail = case patch Proxy d02 (DCons e1 DNil) of
                DCons x DNil -> x

--------------------------------------------------------------------------------

data ExprF xs a where
  Add''   :: ExprF [Expr,Expr] Expr
  Times'' :: ExprF [Expr,Expr] Expr
  If''    :: ExprF [Expr, Expr,Expr] Expr
  IVal''  :: ExprF '[Int] Expr
  BVal''  :: ExprF '[Bool] Expr
  Bool''  :: Bool -> ExprF '[] Bool
  Int''   :: Int -> ExprF '[] Int

instance Family ExprF where
  unbuild Add'' (Add e1 e2) = Just $ DCons e1 (DCons e2 DNil)
  unbuild Times'' (Times e1 e2) = Just $ DCons e1 (DCons e2 DNil)
  unbuild If'' (If e0 e1 e2) = Just $ DCons e0 (DCons e1 (DCons e2 DNil))
  unbuild IVal'' (IVal i) = Just (DCons i DNil)
  unbuild BVal'' (BVal b) = Just (DCons b DNil)
  unbuild (Int'' i) _ = Just DNil
  unbuild (Bool'' b) _ = Just DNil
  unbuild _ _ = Nothing 

  build Add'' (DCons e1 (DCons e2 DNil)) = Add e1 e2
  build Times'' (DCons e1 (DCons e2 DNil)) = Times e1 e2
  build If'' (DCons e0 (DCons e1 (DCons e2 DNil))) = If e0 e1 e2 
  build IVal'' (DCons i DNil) = IVal i
  build BVal'' (DCons b DNil) = BVal b
  build (Int'' i) DNil = i
  build (Bool'' b) DNil = b
  
  string Add'' = "Add"
  string (Int'' i) = show i
  string (Bool'' b) = show b
  string IVal'' = "IVal"
  string BVal'' = "BVal"
  string If''   = "If"
  string Times'' = "Times"

  decEq (Int'' _) (Int'' _) = Just Refl
  decEq (Bool'' _) (Bool'' _) = Just Refl
  decEq IVal'' IVal'' = Just Refl
  decEq IVal'' BVal'' = Just Refl
  decEq IVal'' Times'' = Just Refl
  decEq IVal'' Add'' = Just Refl
  decEq IVal'' If'' = Just Refl
  decEq BVal'' IVal'' = Just Refl
  decEq BVal'' BVal'' = Just Refl
  decEq BVal'' Times'' = Just Refl
  decEq BVal'' Add'' = Just Refl
  decEq BVal'' If'' = Just Refl
  decEq Times'' IVal'' = Just Refl
  decEq Times'' BVal'' = Just Refl
  decEq Times'' Times'' = Just Refl
  decEq Times'' Add'' = Just Refl
  decEq Times'' If'' = Just Refl
  decEq Add'' IVal'' = Just Refl
  decEq Add'' Add'' = Just Refl
  decEq Add'' Times'' = Just Refl
  decEq Add'' If'' = Just Refl
  decEq If'' IVal'' = Just Refl
  decEq If'' Times'' = Just Refl
  decEq If'' Add'' = Just Refl
  decEq If'' If'' = Just Refl
  decEq _ _ = Nothing

  (=?=) (Int'' x) (Int'' y) = if x == y then Just (Refl, Refl) else Nothing
  (=?=) (Bool'' x) (Bool'' y) = if x == y then Just (Refl, Refl) else Nothing
  (=?=) IVal'' IVal'' = Just (Refl, Refl)
  (=?=) BVal'' BVal'' = Just (Refl, Refl)
  (=?=) Times'' Times'' = Just (Refl, Refl)
  (=?=) Add'' Add'' = Just (Refl, Refl)
  (=?=) If'' If'' = Just (Refl, Refl)
  (=?=) _    _    = Nothing


instance Expr :<: ExprF where
  view _ (Add e1 e2) = View Add'' $ DCons e1 $ DCons e2 DNil
  view _ (Times e1 e2) = View Times'' $ DCons e1 $ DCons e2 DNil
  view _ (If e1 e2 e3) = View If'' $ DCons e1 $ DCons e2 $ DCons e3 DNil
  view _ (BVal b) = View BVal'' $ DCons b DNil
  view _ (IVal i) = View IVal'' $ DCons i DNil

instance Bool :<: ExprF where
  view _ b = View (Bool'' b) DNil

instance Int :<: ExprF where
  view _ i = View (Int'' i) DNil

instance Metric ExprF where
  distance (Int'' x) (Int'' y) = if x == y then 0 else 1
  distance (Bool'' x) (Bool'' y) = if x == y then 0 else 1
  distance If'' If'' = 0
  distance Times'' Times'' = 0
  distance Add'' Add'' = 0
  distance BVal'' BVal'' = 0
  distance IVal'' IVal'' = 0
  distance _ _ = 1 -- Here we could defined more fine-grained distances

