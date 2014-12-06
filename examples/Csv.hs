{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Csv where

import Format.Base
import Format.Combinator
import Format.HList
import Text.Parsec.Prim

data Csv = Csv [[Int]]
  deriving Show

-- | Unwraps a proper HList and build a Csv
csv :: HList '[ [[Int]] ] -> Csv
csv = huncurry Csv 

instance Proj Csv '[ [[ Int ]] ] where
  proj (Csv xs) = Just $ Cons xs Nil

-- | Targets a raw HList '[ [[Int]] ]
rawFormat :: Format String '[ [[Int]] ]
rawFormat = sepBy row (Meta '\n')
  where row = sepBy int (Meta ',')

-- | Targets directly the CSV data type
csvFormat :: Format String '[ Csv ]
csvFormat = DF $ csv <$> rawFormat

-- | We can target directly the user-defined data type
csvParser :: Parser String (HList '[ Csv ])
csvParser = mkParser csvFormat

-- | Once the content of a data-type is added in an HList 
-- we can print directly from the user data-type.
csvPrinter :: Printer String (HList '[ Csv ])
csvPrinter = mkPrinter csvFormat

csvText :: String
csvText = csvRow1 ++ "\n" ++ csvRow2
  where csvRow1 = "1,2,3"
        csvRow2 = "4,5,6"

main :: IO ()
main = parseTest csvParser csvText
