{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Csv where

import Control.Isomorphism.Partial

import Data.HList

import Format.Base
import Format.Combinator
import Format.Char
import Format.Prim

import qualified Text.Parsec.Prim as P


--------------------------------------------------------------------------------
-- | Csv specification as Grammar
csvGrammar :: Format String '[Int, [Int], [Int], [[Int]]]
csvGrammar = csvRow <@> many (tag '\n' @> csvRow)
  where csvRow = int <@> many (tag ',' @> int)

--------------------------------------------------------------------------------

-- An algebraic data type that represents a Csv table
data Csv = Csv [[Int]]
  deriving Show

-- | Isomorphism for Csv data type
csv :: CIso '[ [[Int]] ] Csv 
csv = iso (happly Csv) proj (SCons SNil)
  where proj (Csv xss) = Just $ Cons xss Nil

-- | A format that targets a raw HList '[ [[Int]] ]
rawFormat :: Format String '[ [[Int]] ]
rawFormat = sepBy row newline
  where row = sepBy int (tag ',')

-- | A format that targets directly the CSV data type
csvFormat :: SFormat String Csv
csvFormat = csv <$> rawFormat

-- TODO add utility functions to hide the packing/unpacking for singleton HList

-- | We can target directly the user-defined data type
csvParser :: Parser String (HList '[ Csv ])
csvParser = mkParser csvFormat

-- | Once the content of a data-type is added in an HList 
-- we can print directly from the user data-type.
csvPrinter :: Printer String (HList '[ Csv ])
csvPrinter = mkPrinter csvFormat

--------------------------------------------------------------------------------
-- A string containing a well-formed csv table
csvText :: String
csvText = csvRow1 ++ "\n" ++ csvRow2
  where csvRow1 = "1,2,3"
        csvRow2 = "4,5,6"

csv1 :: Csv
csv1 = Csv [[1,2,3],[4,5,6]]

main :: IO ()
main = do
  roundTrip csvFormat csvText
  roundTrip csvGrammar csvText
