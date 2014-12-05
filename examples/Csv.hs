{-# LANGUAGE DataKinds #-}

module Csv where

import Format.Base
import Format.Combinator
import Format.HList
import Data.Functor
import Text.Parsec.Prim

data Csv = Csv [[Int]]
  deriving Show

csvFormat :: Format String '[ [[Int]] ]
csvFormat = Many (csvRow <@ Meta '\n') -- TODO Some
  where csvRow = Many (int <@ Meta ',')

-- | Unwraps a proper HList and build a Csv
toCsv :: HList '[ [[Int]] ] -> Csv
toCsv = huncurry Csv 

-- | We can target directly the user-defined data type
csvParser :: Parser String Csv
csvParser = toCsv <$> mkParser csvFormat

-- | Once the content of a data-type is added in an HList 
-- we can print directly from the user data-type.
csvPrinter :: Printer String Csv
csvPrinter (Csv xss) = mkPrinter csvFormat $ Cons xss Nil

csvText :: String
csvText = unlines [csvRow1, csvRow2]
  where csvRow1 = "1,2,3"
        csvRow2 = "4,5,6"

main :: IO ()
main = parseTest csvParser csvText
 

foo :: Format String '[]
foo = Many (Meta 'a')
