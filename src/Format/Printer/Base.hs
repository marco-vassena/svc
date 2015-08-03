{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Format.Printer.Base where

import Format.Syntax
import Control.Monad
import Data.TypeList.HList

class PrintWith s (m :: * -> *) (i :: *) a where
  mkPrinter' :: a m i xs -> HList xs -> m s

-- This function simply calls @mkPrinter'@, but it should be used instead
-- as it instantiate the constraint type variable properly.
-- Using directly mkPrinter' can indeed lead to ambiguous variables, preventing
-- type inference and requiring explicit type signatures.
mkPrinter :: Use a (PrintWith s) m i => a (PrintWith s) m i xs -> HList xs -> m s
mkPrinter = mkPrinter'
