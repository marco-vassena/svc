{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Format.Parser.Attoparsec where

import Format.Parser.Base
import Format.Parser.GParser
import Data.Attoparsec.ByteString.Char8

instance ParseSatisfy Parser Char where
  parseSatisfy = satisfy

instance ParseHelp Parser where
  parseHelp = (<?>)

instance ParseTry Parser where
  parseTry = try
