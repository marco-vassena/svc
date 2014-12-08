{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

-- This module defines typed heterogeneous lists
-- and few basic functions to deal with them.

module Format.HList where

import GHC.TypeLits
import Data.Proxy

-- Heterogeneous list, indexed by a type level list that
-- mantains the types of the elements contained.
data HList (xs :: [ * ]) where
  Nil :: HList '[]
  Cons :: x -> HList xs -> HList (x ': xs)

-- Type level append
type family Append (xs :: [ * ]) (ys :: [ * ]) :: [ * ] where
  Append '[] ys = ys
  Append (x ': xs) ys = x ': Append xs ys

-- Type level map 
type family Map (f :: * -> *) (xs :: [ * ]) :: [ * ] where
  Map f '[] = '[]
  Map f (x ': xs) = f x ': Map f xs

-- Appends two heterogeneous lists
happend :: HList xs -> HList ys -> HList (Append xs ys)
happend Nil ys = ys
happend (Cons x xs) ys = Cons x (happend xs ys)

-- map for heterogeneous lists
hmap :: (forall a . a -> f a) -> HList xs -> HList (Map f xs)
hmap f Nil = Nil
hmap f (Cons x xs) = Cons (f x) (hmap f xs)

hmap' :: SList xs -> (forall a . f a -> f a) -> HList (Map f xs) -> HList (Map f xs)
hmap' SNil f Nil = Nil
hmap' (SCons s) f (Cons x xs) = Cons (f x) (hmap' s f xs)

-- Returns a singleton 'HList'
hsingleton :: a -> HList '[ a ]
hsingleton a = Cons a Nil

--------------------------------------------------------------------------------
-- The singleton type of lists, which allows us to take a list as a
-- term-level and a type-level argument at the same time.
-- It is used to retrieve information about the shape of an
-- 'HList' at runtime.
data SList xs where
 SNil :: SList '[]
 SCons :: SList xs -> SList (x ': xs)

-- | Append function for the singleton type 'SList'.
sappend :: SList xs -> SList ys -> SList (Append xs ys)
sappend SNil ys = ys
sappend (SCons xs) ys = SCons (sappend xs ys)

-- | Map function for the singleton type SList.
-- This function is lazy in the injecting function.
smap :: (forall a . a -> f a) -> SList xs -> SList (Map f xs)
smap _ SNil = SNil
smap f (SCons xs) = SCons (smap f xs) 

-- A class of objects parametrized over a type level
-- list for which it is possible to produce a 'SList' witness object.
class Reify f where
  toSList :: f xs -> SList xs

--------------------------------------------------------------------------------

-- Concats a list of 'HList' in a single 'HList'.
-- The values contained in the input list are collected in a list.
--
-- > unList (SCons (SCons SNil)) [Cons 1 (Cons 'a' Nil), Cons 2 (Cons 'b' Nil)]
-- > Cons [1,2] (Cons "ab" Nil)
--
unList :: SList xs -> [HList xs] -> HList (Map [] xs)
unList SNil _ = Nil
unList (SCons s) [] = Cons [] (unList s [])
unList s (x:xs) = hmap' s reverse hs
  where hs = foldr (merge s) (hmap (:[]) x) xs

-- | Converts an 'HList' of lists in a list of 'HList' containing
-- each one containing a single element of the original lists.
-- The lists in the 'HList' are supposed to have the same length,
-- if this is not the case only the number of values of the shortest
-- will be retained.
--
-- > toList (SCons (SCons SNil)) (Cons [1,2] (Cons "ab" Nil))
-- > [Cons 1 Cons 'a' Nil,Cons 2 Cons 'b' Nil]
--
toList :: SList xs -> HList (Map [] xs) -> [HList xs]
toList SNil Nil = [Nil] -- TODO also [] would work, distinguish between Many and Some
toList (SCons SNil) (Cons xs Nil) = zipWith Cons xs (repeat Nil)
toList (SCons s) (Cons xs xss) = zipWith Cons xs (toList s xss)

-- | 'merge s xs xss' is equivalent to 'zipWith (:) xs xss' for normal lists
--
-- > merge (SCons (SCons SNil)) (Cons 1 (Cons 'a' Nil)) (Cons [2,3] (Cons "bc" Nil))
-- > Cons [1,2,3] Cons "abc" Nil
--
merge :: SList xs -> HList xs -> HList (Map [] xs) -> HList (Map [] xs)
merge SNil Nil Nil = Nil
merge (SCons s) (Cons x xs) (Cons ys yss) = Cons (x : ys) (merge s xs yss)
  
-- Splits an hlist in two sub-hlists, according to the given index as 'SList'.
split :: SList xs -> SList ys -> HList (Append xs ys) -> (HList xs, HList ys)
split SNil s hs = (Nil, hs)
split (SCons s1) s2 (Cons h hs) = (Cons h hs1, hs2)
  where (hs1, hs2) = split s1 s2 hs

-- Apply an uncurried function to an heterogeneous list.
-- This function is type safe and will result in a missing
-- instance if the function arguments types don't match with 
-- the types of the values contained in the list.
-- 
-- > f :: Int -> Char -> String -> String
-- > f x c s = show x ++ show c ++ s
-- > 
-- > input :: HList '[ Int, Char, String]
-- > input = Cons 1 $ Cons 'a' $ Cons "foo" $ Nil
-- > 
-- > foobar :: String
-- > foobar = (huncurry f) input
class HUncurry a xs c where
  huncurry :: a -> HList xs -> c

instance HUncurry a '[] a where
  huncurry x Nil = x

instance HUncurry b xs c => HUncurry (a -> b) (a ': xs) c where
  huncurry f (Cons x xs) = huncurry (f x) xs

--------------------------------------------------------------------------------
-- Debugging
instance Show (HList '[]) where
  show Nil = "Nil"

instance (Show x, Show (HList xs)) => Show (HList (x ': xs)) where
  show (Cons x xs) = unwords ["Cons", show x, show xs]
