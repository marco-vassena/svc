{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

module Format.Printer.Base where

import Format.Base
import Control.Monad
import Control.Applicative
import Control.Isomorphism.Partial
import Data.HList
import Data.Monoid

type family StreamOf (i :: *)  -- TODO make this associated to class

-- Printing using a format
class PrintFormat m i where
  mkPrinter :: Format m i xs -> HList xs -> m (StreamOf i)

class PrintToken m i s where
  printToken :: i -> m s

instance (PrintToken m i (StreamOf i), Monoid (StreamOf i), MonadPlus m, Applicative m)
   => PrintFormat m i where

  mkPrinter (Seq f1 f2) hs = mappend <$> mkPrinter f1 hs1 <*> mkPrinter f2 hs2
    where (hs1, hs2) = split (toSList f1) (toSList f2) hs
  mkPrinter (CFormat i f) xs = 
    case unapply i xs of
      Nothing -> fail "Deconstructor failed"
      Just ys -> mkPrinter f ys
  mkPrinter (Alt f1 f2) a = mplus (mkPrinter f1 a) (mkPrinter f2 a)
  mkPrinter (Fail _) _ = fail "Unknown printing error"
  mkPrinter Token (Cons t _) = printToken t
  mkPrinter (Pure hs) _ = return mempty
  mkPrinter (Bind s f1 k) hs = mappend <$> mkPrinter f1 hs1 <*> mkPrinter f2 (hs2)
    where (hs1, hs2) = split (toSList f1) s hs
          f2 = k hs1
