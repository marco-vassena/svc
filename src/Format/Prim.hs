-- Utility functions to print and parse with formats

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Format.Prim where

import Format.Base
import Data.HList
import Data.Monoid
import qualified Text.Parsec as P
import Control.Applicative

--------------------------------------------------------------------------------
-- Mainly used for testing

parseTest :: StreamChar i => Format i a -> i -> IO (HList a)
parseTest f input = either (fail . show) return (P.parse (p <* P.eof) "" input)
  where p = mkParser f
   
printTest :: (Monoid i, Show i) => Format i a -> (HList a) -> IO ()
printTest f a = maybe (fail "Printer Failed") print (p a)
  where p = mkPrinter f

-- Parse something and prints it right away using the given format.
roundTrip :: (Show i, Monoid i, StreamChar i) => Format i a -> i -> IO ()
roundTrip f input = parseTest f input >>= printTest f
