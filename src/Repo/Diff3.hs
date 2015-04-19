{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Repo.Diff3 where

import Data.List

-- A generic well-typed representation of a data-type
data DTree a where
  Node :: (Family f, ShowDT sig) => f sig res -> DList DTree sig -> DTree res

instance Show (DTree a) where
  show (Node c args) = "Node " ++ show c ++ " [" ++ xs ++ "]"
    where xs = concat $ intersperse ", " (dmap show args)

dmap :: (forall x . f x -> a) -> DList f xs -> [ a ]
dmap f DNil = []
dmap f (DCons x xs) = f x : dmap f xs

class ShowDT sig where
  
instance ShowDT '[] where
instance (Show (DTree a), ShowDT xs) => ShowDT (a ': xs) where

-- A typed list that contains the children (arguments) of a constructor.
data DList f xs where
  DNil :: DList f '[]
  DCons :: f a -> DList f as -> DList f (a ': as)

class TreeLike a where
  toTree :: a -> DTree a
  fromTree :: DTree a -> a



--------------------------------------------------------------------------------
-- Use case

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

instance TreeLike Expr where
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

instance TreeLike Int where
  toTree i = Node (Int'' i) DNil -- Not so sure this makes sense
  fromTree (Node f DNil) = apply f DNil

instance TreeLike Bool where
  toTree b = Node (Bool'' b) DNil
  fromTree (Node f DNil) = apply f DNil

class Family f where
  apply :: f xs a -> DList DTree xs -> a
  string :: f xs a -> String

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

instance Family f => Show (f sig a) where
  show c = string c
