{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Format.Parser.Attoparsec where

import Format.Syntax.Help (Help(..))
import Format.Parser.Base
import Format.Parser.GParser
import Data.Attoparsec.ByteString.Char8

instance ParseSatisfy Parser Char where
  parseSatisfy = satisfy

instance ParseWith Parser i (Help ParseWith) where
  mkParser' (Help f msg) = (mkParser' f) <?> msg
