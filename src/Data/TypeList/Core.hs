{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Data.TypeList.Core where

-- Type level append
type family (:++:) (xs :: [ * ]) (ys :: [ * ]) :: [ * ] where
  (:++:) '[] ys = ys
  (:++:) (x ': xs) ys = x ': (:++:) xs ys

-- Type level map 
type family Map (f :: * -> *) (xs :: [ * ]) :: [ * ] where
  Map f '[] = '[]
  Map f (x ': xs) = f x ': Map f xs

-- Type level zip
type family ZipWith (f :: * -> * -> *) (xs :: [ * ]) (ys :: [ * ]) where
  ZipWith f '[] '[] = '[]
  ZipWith f (x ': xs) (y ': ys) = f x y ': ZipWith f xs ys
  ZipWith f  xs ys  = '[]

--------------------------------------------------------------------------------
