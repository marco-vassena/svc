{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}

module Format.Parser.Parsec where

import Control.Isomorphism.Partial
import Control.Applicative ((<$>), (<*>), pure)
import Data.HList
import Format.Syntax.Help (Help(..))
import Format.Parser.Base
import Format.Parser.GParser
import Text.Parsec

instance Stream s m Char => ParseSatisfy (ParsecT s u m) Char where
  parseSatisfy = satisfy

instance ParseWith (ParsecT s u m) i (Help ParseWith) where
  mkParser' (Help f msg) = (mkParser' f) <?> msg
