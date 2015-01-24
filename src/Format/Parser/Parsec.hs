{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}

module Format.Parser.Parsec where

import Control.Isomorphism.Partial
import Control.Applicative ((<$>), (<*>), pure)
import Data.HList
import Format.Base hiding (satisfy)
import Format.Parser.Base
import Format.Parser.GParser
import Text.Parsec

instance (Stream s m t, Show t) => ParseToken (ParsecT s u m) t where
  parseToken = anyToken

instance Stream s m Char => ParseSatisfy (ParsecT s u m) Char where
  parseSatisfy = satisfy
