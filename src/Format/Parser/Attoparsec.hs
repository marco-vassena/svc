{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Format.Parser.Attoparsec where

import Format.Parser.Base
import Format.Parser.GParser
import Data.Attoparsec.ByteString.Char8

instance ParseToken Parser Char where
  parseToken = anyChar
