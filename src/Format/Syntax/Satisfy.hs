{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

module Format.Syntax.Satisfy where

import Format.Syntax.Base
import Data.TypeList.HList

data Satisfy c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Satisfy :: (i -> Bool) -> Satisfy c m i '[i]

satisfy :: (Use Format c m i, Use Satisfy c m i) => (i -> Bool) -> Format c m i '[i]
satisfy = format . Satisfy

type SatisfyC c m i = (Use Format c m i, Use Satisfy c m i)

instance Reify (Satisfy c m i) where
  toSList (Satisfy _) = SCons SNil
