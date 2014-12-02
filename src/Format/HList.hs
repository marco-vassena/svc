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

data HList (xs :: [ * ]) where
  Nil :: HList '[]
  Cons :: x -> HList xs -> HList (x ': xs)
 
type family Append (xs :: [ * ]) (ys :: [ * ]) :: [ * ] where
  Append '[] ys = ys
  Append (x ': xs) ys = x ': Append xs ys

type family Map (f :: * -> *) (xs :: [ * ]) :: [ * ] where
  Map f '[] = '[]
  Map f (x ': xs) = f x ': Map f xs

append :: HList xs -> HList ys -> HList (Append xs ys)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

hmap :: (forall a . a -> f a) -> HList xs -> HList (Map f xs)
hmap f Nil = Nil
hmap f (Cons x xs) = Cons (f x) (hmap f xs)

hmap' :: SList xs -> (forall a . f a -> f a) -> HList (Map f xs) -> HList (Map f xs)
hmap' SNil f Nil = Nil
hmap' (SCons s) f (Cons x xs) = Cons (f x) (hmap' s f xs)

hsingleton :: a -> HList '[ a ]
hsingleton a = Cons a Nil

-- The singleton type of lists, which allows us to take a list as a
-- term-level and a type-level argument at the same time (although
-- we're not interested in the elements here, only the structure)
data SList xs where
 SNil :: SList '[]
 SCons :: SList xs -> SList (x ': xs)

sappend :: SList xs -> SList ys -> SList (Append xs ys)
sappend SNil ys = ys
sappend (SCons xs) ys = SCons (sappend xs ys)

-- This function is lazy in the injecting function.
smap :: (forall a . a -> f a) -> SList xs -> SList (Map f xs)
smap _ SNil = SNil
smap f (SCons xs) = SCons (smap f xs) 

--------------------------------------------------------------------------------

unlist :: SList xs -> [HList xs] -> HList (Map [] xs)
unlist SNil _ = Nil
unlist (SCons s) [] = Cons [] (unlist s [])
unlist s (x:xs) = hmap' s reverse hs
  where hs = foldr (merge s) (hmap (:[]) x) xs

merge :: SList xs -> HList xs -> HList (Map [] xs) -> HList (Map [] xs)
merge SNil Nil Nil = Nil
merge (SCons s) (Cons x xs) (Cons ys yss) = Cons (x : ys) (merge s xs yss)
  

-- Apply an uncurried function to an heterogeneous list.
-- This function is type safe and will result in a missing
-- instance if the type of the function and of the list don't match.
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
