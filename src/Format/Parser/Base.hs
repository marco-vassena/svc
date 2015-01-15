{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module Format.Parser.Base where

import Format.Base
import Data.HList

class ParseFormat m i where
  mkParser :: Format m i xs -> m (HList xs)

class ParseToken m i where
  parseToken :: m i
