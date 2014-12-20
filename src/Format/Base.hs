{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}

-- | This module defines types for describing formats

module Format.Base where

import Control.Isomorphism.Partial
import Data.HList

-- | 'SFormat' stands for Single Format and represents a 'Format'
-- containing only one target type.
type SFormat m i a = Format m i '[ a ]

data Format (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Seq :: Format m i xs -> Format m i ys -> Format m i (Append xs ys)
  Match :: HList xs -> Format m i '[]
  Token :: Format m i '[i]
  CFormat :: Iso args xs -> Format m i args -> Format m i xs
  Alt :: Format m i xs -> Format m i xs -> Format m i xs
  Fail :: SList xs -> Format m i xs

--------------------------------------------------------------------------------
instance Reify (Format i m) where
  toSList (Seq f1 f2) = sappend (toSList f1) (toSList f2)
  toSList (CFormat i _) = sunapply i
  toSList (Alt f1 f2) = toSList f1
  toSList (Match hs) = SNil
  toSList (Fail s) = s
  toSList Token = SCons SNil
