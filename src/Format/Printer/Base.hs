{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Format.Printer.Base where

import Format.Base
import Control.Monad
import Data.HList

class PrintWith s (m :: * -> *) (i :: *) (xs :: [ * ]) a where
  mkPrinter :: a m i xs -> HList xs -> m s

-- TODO consider whether to keep this or not
class PrintToken m i s where
  printToken :: i -> m s

-- Fix some variables
mkPrinter' :: Use a (PrintWith s) m i xs => a (PrintWith s) m i xs -> HList xs -> m s
mkPrinter' = mkPrinter
