{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}

module Data.TypeList.Core where

-- Type level append
type family (:++:) (xs :: [ k ]) (ys :: [ k ]) :: [ k ] where
  '[] :++: ys = ys
  (x ': xs) :++: ys = x ': (xs :++: ys)

-- Type level map 
type family Map (f :: k1 -> k2) (xs :: [ k1 ]) :: [ k2 ] where
  Map f '[] = '[]
  Map f (x ': xs) = f x ': Map f xs

-- Type level zip
type family ZipWith f ys xs where
  ZipWith f '[] '[] = '[]
  ZipWith f (x ': xs) (y ': ys) = f x y ': ZipWith f xs ys

--------------------------------------------------------------------------------
