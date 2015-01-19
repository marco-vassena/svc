{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}

-- | This module defines types for describing formats

module Format.Base where

import Control.Isomorphism.Partial
import Data.HList
import Control.Applicative

-- | 'SFormat' stands for Single Format and represents a 'Format'
-- containing only one target type.
type SFormat m i a = Format m i '[ a ]

data Format (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Seq :: Format m i xs -> Format m i ys -> Format m i (Append xs ys)
  Token :: Format m i '[i]
  CFormat :: Iso args xs -> Format m i args -> Format m i xs
  Alt :: Format m i xs -> Format m i xs -> Format m i xs
  Fail :: SList xs -> Format m i xs
  Pure :: HList xs -> Format m i xs -- Not sure why we would need equality here for printing
  Bind :: SList ys -> Format m i xs -> (HList xs -> Format m i ys) -> Format m i (Append xs ys)

data Seq' a b xs ys i (zs :: [ * ]) where
  Seq' :: a i xs -> b i ys -> SeqA a b xs ys i (Append xs ys)

data Token' (i :: *) (xs :: [ * ]) where
  Token' :: Token' i '[i]
  
data CFormat' f args (i :: *) (xs :: [ * ]) where
  CFormat' :: Iso args xs -> f i args -> CFormat' f args i xs
 
data Alt' f g (i :: *) (xs :: [ * ]) where
  Alt' :: f i xs -> g i xs -> Alt' f g i xs

-- * Bad : So many parameters clutter the format signature
-- I think most of the time they can be automatically inferred,
-- However everything is recorded in the type parameters.
foo :: Seq' Token' Token' '[ i ] '[ i ] i '[i, i]
foo = Seq' Token' Token'

class ParseWith (m :: * -> *) (xs :: [ * ]) (f :: * -> [ * ] -> *) where
  mkParser' :: f i xs -> m (HList xs)
 
--------------------------------------------------------------------------------
instance Reify (Format i m) where
  toSList (Seq f1 f2) = sappend (toSList f1) (toSList f2)
  toSList (CFormat i _) = sunapply i
  toSList (Alt f1 f2) = toSList f1
  toSList (Fail s) = s
  toSList (Pure hs) = toSList hs
  toSList Token = SCons SNil
  toSList (Bind s f k) = sappend (toSList f) s
