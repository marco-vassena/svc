{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Format.Parser.Base where

import Format.Base
import Data.HList

class ParseWith (m :: * -> *) (i :: *) (xs :: [ * ]) a where
  mkParser :: a m i xs -> m (HList xs)
 
-- TODO consider whether to keep this or not
class ParseToken m i where
  parseToken :: m i
