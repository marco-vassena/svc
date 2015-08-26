{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Format.Printer.Base where

import Format.Syntax
import Control.Monad
import Data.TypeList.HList

-- | The class @PrintWith s m i a@ represents the printing semantics:
-- 
-- * @s@ is the stream type
-- * @m@ is the printer data type
-- * @i@ is the token type
-- * @a@ is the format descriptor whose printing semantics is given
--
class PrintWith s (m :: * -> *) (i :: *) a where
  mkPrinter' :: a m i xs -> HList xs -> m s

-- | Entry point to be used instead of @mkPrinter'@.
-- It fixes the constraint type variable, thus avoiding ambiguities.
mkPrinter :: Use a (PrintWith s) m i => a (PrintWith s) m i xs -> HList xs -> m s
mkPrinter = mkPrinter'
