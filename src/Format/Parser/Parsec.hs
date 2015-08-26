{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}

module Format.Parser.Parsec where

-- This module contains the hook instances for Parsec

import Control.Isomorphism.Partial
import Control.Applicative ((<$>), (<*>), pure)
import Format.Parser.Base
import Format.Parser.GParser
import Text.Parsec

instance Stream s m Char => ParseSatisfy (ParsecT s u m) Char where
  parseSatisfy = satisfy

instance ParseHelp (ParsecT s u m) where
  parseHelp = (<?>)

instance ParseTry (ParsecT s u m) where
  parseTry = try
