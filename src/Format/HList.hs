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

type family Replicate (n :: Nat) (a :: *) :: [ * ] where
  Replicate 0 a = '[]
  Replicate n a = a ': Replicate (n - 1) a

append :: HList xs -> HList ys -> HList (Append xs ys)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

hmap :: (forall a . a -> f a) -> HList xs -> HList (Map f xs)
hmap f Nil = Nil
hmap f (Cons x xs) = Cons (f x) (hmap f xs)

hconcat :: (HList '[HList xs]) -> HList xs
hconcat (Cons x Nil) = x

hsingleton :: a -> HList '[ a ]
hsingleton a = Cons a Nil

class FromList (n :: Nat) where
  fromList :: [ a ] -> Proxy n -> HList (Replicate n a)

instance FromList 0 where
  fromList [] p = Nil

instance KnownNat n => FromList n where
  fromList xs p = undefined

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

