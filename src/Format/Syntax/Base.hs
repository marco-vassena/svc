{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}

-- | This module defines types for describing formats

module Format.Syntax.Base where

import Prelude ((.), Bool(..), const)
import Control.Isomorphism.Partial
import Data.HList
import Data.Type.Equality
import GHC.Exts

-- TODO stick to alternative/applicative/monad interface
-- in order to provide default obvious implementations.
--  * Add return
--  * Add empty

data Format c (m :: * -> *) (i :: *) (xs :: [*]) where
  Format :: (Reify (a m i), c m i a) => a m i xs -> Format c m i xs

-- | 'SFormat' stands for Single Format and represents a 'Format'
-- containing only one target type.
type SFormat c m i a = Format c m i '[ a ]

data Seq c (m :: * -> *) (i :: *) (zs :: [*]) where
  Seq :: (c m i a, Reify (a m i),
          c m i b, Reify (b m i))
      => a m i xs -> b m i ys -> Seq c m i (Append xs ys)

data Satisfy c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Satisfy :: (i -> Bool) -> Satisfy c m i '[i]
 
data FMap c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  FMap :: (c m i a) => Iso args xs -> a m i args -> FMap c m i xs
 
data Alt c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Alt :: (c m i a, c m i b, Reify (a m i)) 
      =>  a m i xs -> b m i xs -> Alt c m i xs

data Pure c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Pure :: HList xs -> Pure c m i xs

data Fail c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Fail :: SList xs -> Fail c m i xs

data Bind c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Bind :: (c m i a, c m i b, Reify (a m i)) 
       => SList ys -> a m i xs -> (HList xs -> b m i ys) -> Bind c m i (Append xs ys)

fail :: (Use Fail c m i, KnownSList xs) => Format c m i xs
fail = format (Fail slist)

type UseAndReify a c m i = (Use a c m i, Reify (a c m i))

type BindC a c m i = (Use Bind      c m i, 
                      Use Format    c m i, 
                      UseAndReify a c m i)

-- In the continuation type we use Format, rather than a generic b, 
-- because otherwise explicit type signatures are needed.
-- This should not be a problem in practice because all the smart constructors
-- return a Format.

(>>=) :: (BindC a c m i, KnownSList ys) 
      => a c m i xs -> (HList xs -> Format c m i ys) -> Format c m i (Append xs ys)
f >>= k = format (Bind slist f k)

type SeqC a b c m i = (UseAndReify a c m i, UseAndReify b c m i, Use Seq c m i) 

(<*>) :: SeqC a b c m i  => a c m i xs -> b c m i ys -> Format c m i (Append xs ys)
a <*> b = format (Seq a b)

(*>) :: SeqC a b c m i => a c m i '[] -> b c m i ys -> Format c m i ys
p *> q = 
  case leftIdentityAppend (toSList q) of
    Refl -> p <*> q

(<*) :: SeqC a b c m i => a c m i xs -> b c m i '[] -> Format c m i xs
p <* q = 
  case rightIdentityAppend (toSList p) of
    Refl -> p <*> q

type AltC a b c m i = (UseAndReify a c m i, 
                       UseAndReify b c m i, 
                       Use Alt       c m i)

infixr 3 <|>
(<|>) :: AltC a b c m i => a c m i xs -> b c m i xs -> Format c m i xs
p <|> q = format (Alt p q)

satisfy :: Use Satisfy c m i => (i -> Bool) -> Format c m i '[i]
satisfy = format . Satisfy

infixr 4 <$>
(<$>) :: (Use FMap c m i, 
          Use a c m i) 
      => Iso args xs -> a c m i args -> Format c m i xs
f <$> x = format (FMap f x)

pure :: Use Pure c m i => HList xs -> Format c m i xs
pure = format . Pure

format :: (Use a c m i, Reify (a c m i)) => a c m i xs -> Format c m i xs
format = Format

type Use a c m i = c m i (a c)

-- Short-hand for common group of constraints, used together
type FunctorC c m i = (Use FMap c m i, Use Format c m i) 
type ApplicativeC c m i = (Use Pure c m i, Use Seq c m i, FunctorC c m i)
type AlternativeC c m i = (ApplicativeC c m i, Use Alt c m i) -- Add empty ?

--------------------------------------------------------------------------------

instance Reify (Seq c m i) where
  toSList (Seq a b) = sappend (toSList a) (toSList b)

instance Reify (Alt c m i) where
  toSList (Alt a b) = toSList a

instance Reify (Format c m i) where
  toSList (Format f) = toSList f

instance Reify (Bind c m i) where
  toSList (Bind s f k) = sappend (toSList f) s

instance Reify (Satisfy c m i) where
  toSList (Satisfy _) = SCons SNil

instance Reify (Pure c m i) where
  toSList (Pure hs) = toSList hs

instance Reify (Fail c m i) where
  toSList (Fail s) = s

instance Reify (FMap c m i) where
  toSList (FMap i f) = sunapply i
