{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}


module Format.Syntax.Monad where

import Data.TypeList.HList
import Format.Syntax.Base 
import Format.Syntax.Applicative

data MonadS c m i xs where
  Return :: HList xs -> MonadS c m i xs
  Fail :: SList xs -> String -> MonadS c m i xs
  Bind :: (c m i a, c m i b, Reify (a m i)) 
       => SList ys -> a m i xs -> (HList xs -> b m i ys) -> MonadS c m i (xs :++: ys)

type MonadC c m i = (Use MonadS c m i, ApplicativeC c m i) -- According to AMP

return :: MonadC c m i => HList xs -> Format c m i xs
return = format . Return

fail :: (MonadC c m i, KnownSList xs) => String -> Format c m i xs
fail s = format (Fail slist s)


(>>=) :: (MonadC c m i, KnownSList ys) 
      => Format c m i xs -> (HList xs -> Format c m i ys) -> Format c m i (xs :++: ys)
f >>= k = format (Bind slist f k)

instance Reify (MonadS c m i) where
  toSList (Return hs) = toSList hs
  toSList (Bind s f k) = sappend (toSList f) s
  toSList (Fail s _) = s
