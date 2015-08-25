{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}

module Format.Syntax.Functor where

import Format.Syntax.Base 
import Control.Isomorphism.Partial

data FunctorS c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  FMap :: c m i a => Iso args xs -> a m i args -> FunctorS c m i xs

type FunctorC c m i = (Use FunctorS c m i, Use Format c m i) 

infixr 4 <$>
(<$>) :: FunctorC c m i => Iso args xs -> Format c m i args -> Format c m i xs
f <$> x = format (FMap f x)

instance Reify (FunctorS c m i) where
  toSList (FMap i f) = sunapply i
