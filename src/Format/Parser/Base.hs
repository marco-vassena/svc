{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Format.Parser.Base where

import Format.Base
import Data.HList

class ParseWith (m :: * -> *) (i :: *) (xs :: [ * ]) a where
  mkParser' :: a m i xs -> m (HList xs)
 
-- Fix the constraint type variable.
mkParser :: Use a ParseWith m i xs => a ParseWith m i xs -> m (HList xs)
mkParser = mkParser'
