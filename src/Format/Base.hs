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
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}

-- | This module defines types for describing formats

module Format.Base where

import Control.Isomorphism.Partial
import Data.HList
import Control.Applicative
import GHC.Exts

-- | 'SFormat' stands for Single Format and represents a 'Format'
-- containing only one target type.
type SFormat m i a = Format m i '[ a ]

--data Format c (m :: * -> *) (i :: *) (xs :: [ * ]) where
--  Format :: c m i xs a => a m i xs -> Format c m i xs
 
data Format (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Seq :: Format m i xs -> Format m i ys -> Format m i (Append xs ys)
  Token :: Format m i '[i]
  CFormat :: Iso args xs -> Format m i args -> Format m i xs
  Alt :: Format m i xs -> Format m i xs -> Format m i xs
  Fail :: SList xs -> Format m i xs
  Pure :: HList xs -> Format m i xs -- Not sure why we would need equality here for printing
  Bind :: SList ys -> Format m i xs -> (HList xs -> Format m i ys) -> Format m i (Append xs ys)

data Seq' c (m :: * -> *) (i :: *) (zs :: [*]) where
  Seq' :: (c m i xs a, c m i ys b) => a m i xs -> b m i ys -> Seq' c m i (Append xs ys)

data Seq'' c (m :: * -> *) (i :: *) (zs :: [*]) where
  Seq'' :: (c m i xs (a c), c m i ys (b c)) => a c m i xs -> b c m i ys -> Seq'' c m i (Append xs ys)

data Token' (c :: (* -> *) -> * -> [ * ] -> ((* -> *) -> * -> [*] -> *) -> Constraint) (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Token' :: Token' c m i '[i]
  
data CFormat' c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  CFormat' :: c m i args a => Iso args xs -> a m i args -> CFormat' c m i xs
 
data Alt' c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Alt' :: (c m i xs a, c m i xs b) => a m i xs -> b m i xs -> Alt' c m i xs

seq' :: (Use a c m i xs, Use b c m i ys) => a c m i xs -> b c m i ys -> Seq' c m i (Append xs ys)
seq' = Seq'

foo :: Use Token' c m i '[i] => Seq' c m i '[i , i]
foo = seq' Token' Token'

bar :: (Use Token' c m i '[i] ,
        Use Seq' c m i '[i, i]) => Seq' c m i '[i, i, i, i] 
bar = seq' foo foo

type Use a c m i xs = c m i xs (a c)

class ParseWith (m :: * -> *) (i :: *) (xs :: [ * ]) a where
  mkParser' :: a m i xs -> m (HList xs)
 
class PrintWith s (m :: * -> *) (i :: *) (xs :: [ * ]) a where
  mkPrinter' :: a m i xs -> HList xs -> m s

class DummyReify m i xs a => PrintAndReify s m i xs a where
  mkPrinter'' :: a m i xs -> HList xs -> m s

class DummyReify m i xs a where
  dummyToSList :: a m i xs -> SList xs
 
instance DummyReify m i xs (Seq' DummyReify) where
  dummyToSList (Seq' f1 f2) = sappend (dummyToSList f1) (dummyToSList f2)

instance Reify (Seq' DummyReify m i) where
  toSList (Seq' f1 f2) = sappend (dummyToSList f1) (dummyToSList f2)

instance DummyReify m i xs (Seq' (PrintAndReify s)) where
  dummyToSList (Seq' f1 f2) = sappend (dummyToSList f1) (dummyToSList f2)

--------------------------------------------------------------------------------
instance Reify (Format m i) where
  toSList (Seq f1 f2) = sappend (toSList f1) (toSList f2)
  toSList (CFormat i _) = sunapply i
  toSList (Alt f1 f2) = toSList f1
  toSList (Fail s) = s
  toSList (Pure hs) = toSList hs
  toSList Token = SCons SNil
  toSList (Bind s f k) = sappend (toSList f) s
