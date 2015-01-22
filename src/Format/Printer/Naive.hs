{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

-- | A naive printer implementation

module Format.Printer.Naive (
    module Format.Printer.Base
  , Printer
  ) where

import Format.Printer.Base
import Data.HList
import Control.Monad

data Printer i xs = Printer { runPrinter :: HList xs -> Maybe i }

instance (Monad m) => PrintToken m Char String where
  printToken = return . (:[])

