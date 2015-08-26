{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

-- | Definition of the satisfy format combinator and its smart constructor.

module Format.Syntax.Satisfy where

import Format.Syntax.Base
import Data.TypeList.HList

-- | Satisfy format combinator
data Satisfy c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Satisfy :: (i -> Bool) -> Satisfy c m i '[i]

-- | Most parsers provide a similar primitive that retrieves 
-- the next token in the stream. 
satisfy :: (Use Format c m i, Use Satisfy c m i) => (i -> Bool) -> Format c m i '[i]
satisfy = format . Satisfy

-- The constraints required to use the Satisfy combinator.
type SatisfyC c m i = (Use Format c m i, Use Satisfy c m i)

instance Reify (Satisfy c m i) where
  toSList (Satisfy _) = SCons SNil
