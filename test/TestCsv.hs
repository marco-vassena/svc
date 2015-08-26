-- Tests that parser and printer are inverse for CSV tables

module Main where

import Data.List
import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Test
import System.Exit
import Csv (Csv(..), parseCsv, csvPrinter)
import Utility

nRows :: Gen Int
nRows = choose (1, 25)

number :: Gen Int
number = choose (0, 10 ^ 9)

-- A wrapper for a string that represents a csv table 
newtype CsvString = CsvString String
  deriving (Show, Eq)

instance Arbitrary CsvString where
  arbitrary = do
    Csv xss <- arbitrary
    let s = intercalate "\n" (map (intercalate "," . map show) xss)
    return (CsvString s)
  
instance Arbitrary Csv where
  arbitrary = do
    n <- nRows
    xss <- listOf $ vectorOf n number
    return (Csv xss)

prop_leftId :: Csv -> Bool
prop_leftId input = input == output
  where output = parseWith (Just . parseCsv) (printWith csvPrinter input)

prop_rightId :: CsvString -> Bool
prop_rightId (CsvString input) = input == output
  where output = printWith csvPrinter (parseWith (Just . parseCsv) input)

main :: IO ()
main = do
  r1 <- quickCheckResult prop_leftId
  r2 <- verboseCheckResult prop_rightId
  if all isSuccess [r1, r2]
    then return ()
    else exitFailure
