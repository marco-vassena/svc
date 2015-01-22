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

import Format.Base
import Format.Printer.Base
import Data.HList
import Format.Printer.GPrinter

type Printer = Maybe

instance (Monad m) => PrintToken m Char String where
  printToken = return . (:[])

instance PrintWith [i] Printer i '[i] (Token (PrintWith [i])) where
  mkPrinter _ (Cons t _) = Just [t]
