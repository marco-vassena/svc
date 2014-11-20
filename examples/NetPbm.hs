{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}

module NetPbm where

import Control.Applicative
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as B
import Data.Foldable
import Data.List
import Data.Proxy
import Data.Word
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

type WhiteSpace = Many (Proxy " " :+: Proxy "\t" :+: Proxy "\n" :+: Proxy "\r")
type PbmMagic = Proxy "P1\n" 
type Comment = Proxy "#" :*: Many (NoneOf "\n") :*: Proxy "\n"
type PbmHeader = PbmMagic :*: Maybe (Comment) :*: WhiteSpace :*: Int :*: WhiteSpace :*: Int :*: WhiteSpace
-- Ascii Portable Bit map
type Pbm = PbmHeader :~>: Image

-- Maybe I could use datatypes a la carte to provide a sort of search mechanism,
-- so that the user can specify only the part of the header that he really needs.
-- In this example an instance for Int :*: WhiteSpace :*: Int would be enough.
instance DecodeWith ByteString PbmHeader Image where
  decodeWith :: PbmHeader -> Parser Image
  decodeWith (_ :*: _ :*:  _ :*: width :*: _ :*: height :*: _) = Image <$> count height parseRow
    where parseRow :: Parser [Bit]
          parseRow = count width (decode <* spaces)

--------------------------------------------------------------------------------

data PgmImage = PgmImage [[ Word8 ]]

type PgmMagic = Proxy "P5" :*: WhiteSpace
type PgmHeader = Int :*: WhiteSpace :*: Int :*: WhiteSpace :*: Int :*: WhiteSpace
-- Binary Portable Gray Map
type Pgm = PgmMagic :*: Maybe Comment :*: (PgmHeader :~>: PgmImage)

instance Encode ByteString PgmImage where
  gencode (PgmImage img) = foldMap (foldMap gencode) img

instance DecodeWith ByteString PgmHeader PgmImage where
  decodeWith (width :*: _ :*: height :*: _ :*: maxVal :*: _) = 
    PgmImage <$> count height (count width decode)

parsePbm :: Parser Pbm
parsePbm = decode

parsePgm :: Parser Pgm
parsePgm = decode

data ImageType = PbmType
               | PgmType

getImageType :: String -> ImageType
getImageType s | "ascii.pbm" `isSuffixOf` s = PbmType
getImageType s | "pgm" `isSuffixOf` s = PgmType
getImageType s | otherwise = error $ "Unsupported format: " ++ s

report :: (DataFormat ByteString a, Show e) => Either e a -> IO ()
report = either print (B.putStr . encode)

test :: String -> IO ()
test f = do
  s <- B.readFile f
  case getImageType f of
    PbmType -> report $ parseFormat parsePbm s
    PgmType -> report $ parseFormat parsePgm s
