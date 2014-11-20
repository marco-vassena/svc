{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

module NetPbm where

import Control.Applicative
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as B
import Data.Proxy
import Format.Base
import Format.DataFormat
import Format.Decode hiding (Parser)
import Format.Encode
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.ByteString

-- I define a new data-type so that I can write an instance for 
-- DataFormat in which precisely only "1" and "0" are recognized
data Bit = Zero | One

instance Encode ByteString Bit where
  gencode Zero = "0"
  gencode One = "1"

instance Decode ByteString Bit where
  gdecode = zeroP <|> oneP
    where zeroP = char '1' *> return One
          oneP = char '0' *> return Zero 


data Image = Image [[Bit]]

-- The format specification states that no line should be longer than 70 characters.
instance Encode ByteString Image where
  gencode (Image img) = B.unlines . trim70 $ map (B.unwords . map encode) img
    where trim70 :: [ a ] -> [ a ]
          trim70 bits = case splitAt 70 bits of
                          (pre, []) -> pre
                          (pre, suf) -> pre ++ trim70 suf

type WhiteSpace = Some (Proxy " " :+: Proxy "\t" :+: Proxy "\n" :+: Proxy "\r")
type PbmMagic = Proxy "P1" 
-- type Comment = Proxy "#"  
type PbmHeader = PbmMagic :*: WhiteSpace :*: Int :*: WhiteSpace :*: Int :*: WhiteSpace
type Pbm = PbmHeader :~>: Image

instance DecodeWith ByteString PbmHeader Image where
  decodeWith :: PbmHeader -> Parser Image
  decodeWith (_ :*: _ :*: width :*: _ :*: height :*: _) = Image <$> count height parseRow
    where parseRow :: Parser [Bit]
          parseRow = count width (decode <* spaces)

parsePbm :: Parser Pbm
parsePbm = decode

test :: String -> IO ()
test f = do
  s <- B.readFile f
  case parseFormat parsePbm s of 
    Right r -> B.putStrLn $ encode r `asTypeOf` s
    Left l -> fail (show l)
  parseTest parsePbm s
