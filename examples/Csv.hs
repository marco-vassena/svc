{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module Csv where

import Control.Applicative
import Data.Attoparsec.ByteString.Char8
import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as B
import Data.Proxy
import Format.Types
import Format.ByteString

type CsvRow = (Many (Int :*: Proxy ",")) :*: Int
type Csv = Many (CsvRow :*: Proxy "\n")

csvRow1, csvRow2 :: ByteString
csvRow1 = "1,2,3"
csvRow2 = "4,5,6"

csv1 :: ByteString
csv1 = B.unlines [csvRow1, csvRow2]

type Foo = Proxy 1 :*: Char

foo1 :: ByteString
foo1 = "1a"

output :: DataFormat ByteString a => Either String a -> IO ()
output (Left s) = putStrLn $ "Failed:\t" ++ s
output (Right r) = putStrLn $ B.unpack $ encode r

main :: IO ()
main = do
  let r = parseFormat decode csv1 :: Either String Csv
  let p = parseFormat decode foo1 :: Either String Foo
  output r
  output p
  

