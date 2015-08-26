{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

-- | Definition of monadic format combinators and their smart constructors.

module Format.Syntax.Monad where

import Data.TypeList.HList
import Format.Syntax.Base 
import Format.Syntax.Applicative

-- | Monad Format combinators.
data MonadS c m i xs where
  Return :: HList xs -> MonadS c m i xs
  Fail :: SList xs -> String -> MonadS c m i xs
  Bind :: (c m i a, c m i b, Reify (a m i)) 
       => SList ys -> a m i xs -> (HList xs -> b m i ys) -> MonadS c m i (xs :++: ys)

-- | The constraints required to use the monadic combinators.
-- Following the AMP, the applicative constraints are also included.
type MonadC c m i = (Use MonadS c m i, ApplicativeC c m i)

-- | Lifts a list of values in the monadic format.
return :: MonadC c m i => HList xs -> Format c m i xs
return = format . Return

-- | Aborts the computation with an error message.
fail :: (MonadC c m i, KnownSList xs) => String -> Format c m i xs
fail s = format (Fail slist s)

-- | Binds two computation together, providing the result of the first to the second.
-- Contrary to the standard @Monad@ bind, the resulting index contains not only
-- the second list, but also the first. This is needed to correctly invert
-- the format in the printing semantics. Otherwise it would require
-- to invert somehow the dependency embodied by the second format.
(>>=) :: (MonadC c m i, KnownSList ys) 
      => Format c m i xs -> (HList xs -> Format c m i ys) -> Format c m i (xs :++: ys)
f >>= k = format (Bind slist f k)

instance Reify (MonadS c m i) where
  toSList (Return hs) = toSList hs
  toSList (Bind s f k) = sappend (toSList f) s
  toSList (Fail s _) = s
