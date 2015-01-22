{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-} -- remove

-- | This module defines types for describing formats

module Format.Base where

import Prelude ((.))
import Control.Isomorphism.Partial
import Data.HList
import Data.Type.Equality
import GHC.Exts

-- TODO stick to alternative/applicative/monad interface
-- in order to provide default obvious implementations.
--  * Add return
--  * Add empty

data Format c (m :: * -> *) (i :: *) (xs :: [*]) where
  Format :: (c m i xs a, Reify (a m i)) => a m i xs -> Format c m i xs

-- | 'SFormat' stands for Single Format and represents a 'Format'
-- containing only one target type.
type SFormat c m i a = Format c m i '[ a ]

data Seq c (m :: * -> *) (i :: *) (zs :: [*]) where
  Seq :: (c m i xs a, Reify (a m i), 
          c m i ys b, Reify (b m i)) 
      => a m i xs -> b m i ys -> Seq c m i (Append xs ys)

data Token (c :: (* -> *) -> * -> [ * ] -> ((* -> *) -> * -> [*] -> *) -> Constraint)
           (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Token :: Token c m i '[i]
  
data FMap c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  FMap :: (c m i args a) => Iso args xs -> a m i args -> FMap c m i xs
 
data Alt c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Alt :: (c m i xs a, c m i xs b, Reify (a m i)) 
      =>  a m i xs -> b m i xs -> Alt c m i xs

data Pure c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Pure :: HList xs -> Pure c m i xs

data Fail c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Fail :: SList xs -> Fail c m i xs

data Bind c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  Bind :: (c m i xs a, c m i ys b, Reify (a m i)) 
       => SList ys -> a m i xs -> (HList xs -> b m i ys) -> Bind c m i (Append xs ys)

fail :: (Use Fail c m i xs, KnownSList xs) => Format c m i xs
fail = format (Fail slist)


-- In the continuation type we use Format, rather than a generic b, 
-- because otherwise explicit type signatures are needed.
-- This should not be a problem in practice because all the smart constructors
-- return a Format.
(>>=) :: (Use Bind c m i (Append xs ys), 
          Use a c m i xs, Use Format c m i ys,
          KnownSList ys, Reify (a c m i))
      => a c m i xs -> (HList xs -> Format c m i ys) -> Format c m i (Append xs ys)
f >>= k = format (Bind slist f k)

(<*>) :: (Use a c m i xs, Reify (a c m i),
          Use b c m i ys, Reify (b c m i),
          Use Seq c m i (Append xs ys)) 
      => a c m i xs -> b c m i ys -> Format c m i (Append xs ys)
a <*> b = format (Seq a b)

(*>) :: (Use a c m i '[], Reify (a c m i), 
         Use b c m i  ys, Reify (b c m i),
         Use Seq c m i ys ) 
     => a c m i '[] -> b c m i ys -> Format c m i ys
p *> q = 
  case leftIdentityAppend (toSList q) of
    Refl -> p <*> q

(<*) :: (Use a c m i  xs, Reify (a c m i), 
         Use b c m i '[], Reify (b c m i),
         Use Seq c m i xs ) 
      => a c m i xs -> b c m i '[] -> Format c m i xs
p <* q = 
  case rightIdentityAppend (toSList p) of
    Refl -> p <*> q


infixr 3 <|>
(<|>) :: (Use Alt c m i xs, 
          Use a c m i xs, 
          Use b c m i xs, 
          Reify (a c m i)) 
      => a c m i xs -> b c m i xs -> Format c m i xs
p <|> q = format (Alt p q)

token :: Use Token c m i '[i] => Format c m i '[i]
token = format Token

infixr 4 <$>
(<$>) :: (Use FMap c m i xs, 
          Use a c m i args) 
      => Iso args xs -> a c m i args -> Format c m i xs
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

instance Reify (Fail c m i) where
  toSList (Fail s) = s

instance Reify (Bind c m i) where
  toSList (Bind s f k) = sappend (toSList f) s
