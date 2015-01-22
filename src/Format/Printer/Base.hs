{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Format.Printer.Base where

import Format.Base hiding ((<$>), (<*>))
import Control.Monad
import Control.Applicative
import Control.Isomorphism.Partial
import Data.HList
import Data.Monoid

class PrintWith s (m :: * -> *) (i :: *) (xs :: [ * ]) a where
  mkPrinter :: a m i xs -> HList xs -> m s

-- TODO consider whether to keep this or not
class PrintToken m i s where
  printToken :: i -> m s

-- TODO move to GPrinter
instance (Applicative m, Monoid s) => PrintWith s m i xs (Seq (PrintWith s)) where
  mkPrinter (Seq f1 f2) hs = mappend <$> mkPrinter f1 hs1 <*> mkPrinter f2 hs2
    where (hs1, hs2) = split (toSList f1) (toSList f2) hs
