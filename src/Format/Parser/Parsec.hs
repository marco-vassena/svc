{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}

module Format.Parser.Parsec where

import Control.Isomorphism.Partial
import Control.Applicative ((<$>), (<*>), pure)
import Data.HList
import Format.Base
import Format.Parser.Base
import Format.Parser.GParser
import Text.Parsec

instance (Stream s m t, Show t) => ParseToken (ParsecT s u m) t where
  parseToken = anyToken
