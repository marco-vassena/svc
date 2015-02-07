{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Csv where

import Control.Isomorphism.Partial

import Data.HList

import Format.Syntax hiding (fail)
import Format.Combinator
import Format.Token
import Format.Printer
import Format.Printer.Naive
import Format.Parser
import Format.Parser.UU
import Text.ParserCombinators.UU.BasicInstances
import Text.ParserCombinators.UU.Utils

import Util

--------------------------------------------------------------------------------
-- | Csv specification as Grammar
--------------------------------------------------------------------------------
csvGrammar :: (Use Satisfy c m Char, AlternativeC c m Char, Use Help c m Char) 
           => Format c m Char '[Int, [Int], [Int], [[Int]]]
csvGrammar = csvRow <*> many (char '\n' *> csvRow)
  where csvRow = int <*> many (char ',' *> int)

--------------------------------------------------------------------------------

-- An algebraic data type that represents a Csv table
data Csv = Csv [[Int]]
  deriving (Show, Eq)

-- | Isomorphism for Csv data type
csv :: CIso '[ [[Int]] ] Csv 
csv = iso (happly Csv) proj (SCons SNil)
  where proj (Csv xss) = Just $ Cons xss Nil

-- | A format that targets a raw HList '[ [[Int]] ]
rawFormat :: (Use Satisfy c m Char, Use Help c m Char, AlternativeC c m Char) => Format c m Char '[ [[Int]] ]
rawFormat = sepBy row newline
  where row = sepBy1 int (char ',')

-- | A format that targets directly the CSV data type
csvFormat :: (Use Satisfy c m Char, Use Help c m Char, AlternativeC c m Char) => SFormat c m Char Csv
csvFormat = csv <$> rawFormat

-- TODO add utility functions to hide the packing/unpacking for singleton HList

-- | We can target directly the user-defined data type
csvParser :: Parser (HList '[ Csv ])
csvParser = mkParser csvFormat

-- | Once the content of a data-type is added in an HList 
-- we can print directly from the user data-type.
csvPrinter :: Csv -> Maybe String
csvPrinter = mkPrinter csvFormat . hsingleton

--------------------------------------------------------------------------------
-- A string containing a well-formed csv table
csvText :: String
csvText = csvRow1 ++ "\n" ++ csvRow2
  where csvRow1 = "1,2,3"
        csvRow2 = "4,5,6"

csv1 :: Csv
csv1 = Csv [[1,2,3],[4,5,6]]

parseCsv :: String -> Csv
parseCsv s = 
  case runParser "" csvParser s of 
    Cons csv Nil -> csv

main :: IO ()
main = do
  let csv = parseCsv csvText
  case csvPrinter csv of
    Just s -> putStrLn s
    Nothing -> fail "Printer failed"
