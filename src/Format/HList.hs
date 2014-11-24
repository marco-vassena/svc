{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

-- This module defines typed heterogeneous lists
-- and few basic functions to deal with them.

module Format.HList where

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

