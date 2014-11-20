{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Format.DataFormat where

import Control.Applicative ((<*))
import Control.Monad.Identity
import Data.Monoid
import Format.Base
import Format.Decode
import Format.Encode
import Text.Parsec
import Text.Parsec.Prim
import Text.Parsec.Combinator

-- Used to parse a format described in a DataFormat instance.
-- It requires the whole input to be consumed.
parseFormat :: (DataFormat i a, Stream i Identity t, Show t) => Parser i a -> i -> Either ParseError a
parseFormat p = parse (p <* eof) ""

parseTest :: (DataFormat i a, Stream i Identity t, Show i, Show t) => Parser i a -> i -> IO ()
parseTest p input = 
  case parseFormat p input of
    Left err -> do 
      putStr "parse error at "
      print err
    Right x -> putStrLn $ show $ (encode x) `asTypeOf` input

-- Defines the encoding / decoding functions for a DataFormat
class DataFormat i a where
  decode :: Parser i a
  encode :: a -> i

instance (Encode i a, Decode i a) => DataFormat i a where
  decode = gdecode
  encode = gencode
