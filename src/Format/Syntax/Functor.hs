{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}

-- | Definition of the functor format combinator and its smart constructor.

module Format.Syntax.Functor where

import Format.Syntax.Base 
import Control.Isomorphism.Partial

-- | Functor Format
data FunctorS c (m :: * -> *) (i :: *) (xs :: [ * ]) where
  FMap :: c m i a => Iso args xs -> a m i args -> FunctorS c m i xs

-- The constraints needed to use functor combinators.
type FunctorC c m i = (Use FunctorS c m i, Use Format c m i) 

infixr 4 <$>

-- | @i <$> f@ represents a partial isomorphism applied to a format descriptor.
-- The pure function of @Iso@ is used with the parsing semantics,
-- while the partial inverse function is used when printing.
(<$>) :: FunctorC c m i => Iso args xs -> Format c m i args -> Format c m i xs
f <$> x = format (FMap f x)

instance Reify (FunctorS c m i) where
  toSList (FMap i f) = sunapply i
