{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

module NetPbm where

import Control.Applicative
import Format.Types
import Format.ByteString
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as B
import Data.Attoparsec.ByteString
import Data.Attoparsec.ByteString.Char8
import Data.Proxy

-- I define a new data-type so that I can write an instance for 
-- DataFormat in which precisely only "1" and "0" are recognized
data Bit = Zero | One

instance DataFormat ByteString Bit where
  encode Zero = "0"
  encode One = "1"

  decode = zeroP <|> oneP
    where zeroP = char '1' *> return One
          oneP = char '0' *> return Zero 


data Image = Image [[Bit]]

-- The format specification states that no line should be longer than 70 characters.
instance DataFormat ByteString Image where
  encode (Image img) = B.unlines . trim70 $ map (B.unwords . map encode) img
    where trim70 :: [ a ] -> [ a ]
          trim70 bits = case splitAt 70 bits of
                          (pre, []) -> pre
                          (pre, suf) -> pre ++ trim70 bits
          
    
  decode = undefined -- not used

type WhiteSpace = Proxy " " :+: Proxy "\t" :+: Proxy "\n" :+: Proxy "\r"
type PbmMagic = Proxy "P1" 
type PbmHeader = PbmMagic :*: WhiteSpace :*: Int :*: WhiteSpace :*: Int :*: WhiteSpace
type Pbm = PbmHeader :~>: Image

instance DecodeWith ByteString PbmHeader Image where
  decodeWith :: PbmHeader -> Parser Image
  decodeWith (_ :*: _ :*: height :*: _ :*: width :*: _) = Image <$> count height parseRow
    where parseRow :: Parser [Bit]
          parseRow = count width (decode <* skipSpace)

parsePbm :: Parser Pbm
parsePbm = decode

test :: String -> IO ()
test file  = do
  s <- B.readFile file
  case parseFormat parsePbm s of
    Left s -> fail s
    Right r -> B.putStrLn (encode r)
