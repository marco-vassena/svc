{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

-- Definition of applicative format combinators and their smart constructors.

module Format.Syntax.Applicative where

import Data.Type.Equality
import Data.TypeList.HList
import Format.Syntax.Base 
import Format.Syntax.Functor

-- | Applicative Format
data ApplicativeS c (m :: * -> *) (i :: *) (zs :: [*]) where
  Pure :: HList xs -> ApplicativeS c m i xs
  Star :: (c m i a, Reify (a m i),
          c m i b, Reify (b m i))
      => a m i xs -> b m i ys -> ApplicativeS c m i (xs :++: ys)

-- | The constraints required to use applicative combinators
type ApplicativeC c m i = (Use ApplicativeS c m i, FunctorC c m i)

-- Sequential application.
-- @f <*> g@ is a format composed by the format @f@, followed by the format @g@.
(<*>) :: ApplicativeC c m i => Format c m i xs -> Format c m i ys -> Format c m i (xs :++: ys)
a <*> b = format (Star a b)

-- Sequence two formats, discarding the first.
-- Only /trivial/ formats may be discarded.
(*>) :: ApplicativeC c m i => Format c m i '[] -> Format c m i ys -> Format c m i ys
p *> q =
  case leftIdentityAppend (toSList q) of
    Refl -> p <*> q

-- Sequence two formats, discarding the second.
-- Only /trivial/ formats may be discarded.
(<*) :: ApplicativeC c m i => Format c m i xs -> Format c m i '[] -> Format c m i xs
p <* q = 
  case rightIdentityAppend (toSList p) of
    Refl -> p <*> q

-- Lifts a list in the parsing/printing applicative functor.
pure :: Use ApplicativeS c m i => HList xs -> Format c m i xs
pure = format . Pure

instance Reify (ApplicativeS c m i) where
  toSList (Pure hs) = toSList hs
  toSList (Star a b) = sappend (toSList a) (toSList b)
