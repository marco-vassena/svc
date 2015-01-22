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

import Prelude ((.))
import Control.Isomorphism.Partial
import Data.HList
import Data.Type.Equality
import GHC.Exts

-- | 'SFormat' stands for Single Format and represents a 'Format'
-- containing only one target type.
type SFormat c m i a = Format c m i '[ a ]

--data Format c (m :: * -> *) (i :: *) (xs :: [ * ]) where
--  Format :: c m i xs a => a m i xs -> Format c m i xs
 
--data Format (m :: * -> *) (i :: *) (xs :: [ * ]) where
--  Seq :: Format m i xs -> Format m i ys -> Format m i (Append xs ys)
--  Token :: Format m i '[i]
--  FMap :: Iso args xs -> Format m i args -> Format m i xs
--  Alt :: Format m i xs -> Format m i xs -> Format m i xs
--  Fail :: SList xs -> Format m i xs
--  Pure :: HList xs -> Format m i xs -- Not sure why we would need equality here for printing
--  Bind :: SList ys -> Format m i xs -> (HList xs -> Format m i ys) -> Format m i (Append xs ys)

data Format c (m :: * -> *) (i :: *) (xs :: [*]) where
  Format :: (c m i xs a, Reify (a m i)) => a m i xs -> Format c m i xs

data Seq c (m :: * -> *) (i :: *) (zs :: [*]) where
  Seq :: (c m i xs a, Reify (a m i), 
          c m i ys b, Reify (b m i)) => a m i xs -> b m i ys -> Seq c m i (Append xs ys)

data Token (c :: (* -> *) -> * -> [ * ] -> ((* -> *) -> * -> [*] -> *) -> Constraint)
           (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Token :: Token c m i '[i]
  
data FMap c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  FMap :: (c m i args a) => Iso args xs -> a m i args -> FMap c m i xs
 
data Alt c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Alt :: (c m i xs a, c m i xs b, Reify (a m i)) => a m i xs -> b m i xs -> Alt c m i xs

data Pure c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Pure :: HList xs -> Pure c m i xs

(<*>) :: (Use a c m i xs, Reify (a c m i),
          Use b c m i ys, Reify (b c m i),
          Use Seq c m i (Append xs ys)) => a c m i xs -> b c m i ys -> Format c m i (Append xs ys)
a <*> b = format (Seq a b)

(*>) :: (Use a c m i '[], Reify (a c m i), 
         Use b c m i  ys, Reify (b c m i),
         Use Seq c m i ys ) => a c m i '[] -> b c m i ys -> Format c m i ys
p *> q = 
  case leftIdentityAppend (toSList q) of
    Refl -> p <*> q

(<*) :: (Use a c m i  xs, Reify (a c m i), 
         Use b c m i '[], Reify (b c m i),
         Use Seq c m i xs ) => a c m i xs -> b c m i '[] -> Format c m i xs
p <* q = 
  case rightIdentityAppend (toSList p) of
    Refl -> p <*> q


infixr 3 <|>
(<|>) :: (Use Alt c m i xs, 
          Use a c m i xs, 
          Use b c m i xs, 
          Reify (a c m i)) => a c m i xs -> b c m i xs -> Format c m i xs
p <|> q = format (Alt p q)

token :: Use Token c m i '[i] => Format c m i '[i]
token = format Token

infixr 4 <$>
(<$>) :: (Use FMap c m i xs, Use a c m i args) => Iso args xs -> a c m i args -> Format c m i xs
f <$> x = format (FMap f x)

pure :: Use Pure c m i xs => HList xs -> Format c m i xs
pure = format . Pure

format :: (Use a c m i xs, Reify (a c m i)) => a c m i xs -> Format c m i xs
format = Format

type Use a c m i xs = c m i xs (a c)

instance Reify (Token c m i) where
  toSList Token = SCons SNil

instance Reify (Seq c m i) where
  toSList (Seq a b) = sappend (toSList a) (toSList b)

instance Reify (Alt c m i) where
  toSList (Alt a b) = toSList a

instance Reify (FMap c m i) where
  toSList (FMap i f) = sunapply i

instance Reify (Format c m i) where
  toSList (Format f) = toSList f

instance Reify (Pure c m i) where
  toSList (Pure hs) = toSList hs
--------------------------------------------------------------------------------
