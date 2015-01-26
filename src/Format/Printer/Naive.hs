{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

-- | A naive printer implementation

module Format.Printer.Naive (
    module Format.Printer.Base
  , Printer
  ) where

import Control.Applicative

import Data.HList
import Data.ByteString.Char8

import Format.Syntax.Help
import Format.Printer.Base
import Format.Printer.GPrinter

type Printer = Maybe

instance (Applicative m) => PrintToken m i [i] where
  printToken = pure . (:[])

instance (Applicative m) => PrintToken m Char ByteString where
  printToken = pure . singleton

instance PrintWith s m i (Help (PrintWith s)) where
  -- It is always safe to just ignore the message
  mkPrinter' (Help f msg) = mkPrinter' f


