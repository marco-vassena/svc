{-# LANGUAGE MultiParamTypeClasses #-}

module Format.Printer where

import Format.Base
import Data.HList

-- Printing using a format
class PrintFormat m i where
  printToken :: m i
  mkPrinter :: Format m i xs -> HList xs -> m i

--mkPrinter :: Monoid i => Format m i xs -> HList xs -> m i
--mkPrinter (Seq f1 f2) hs = mappend <$> mkPrinter f1 hs1 <*> mkPrinter f2 hs2
--  where (hs1, hs2) = split (toSList f1) (toSList f2) hs
--mkPrinter (CFormat i f) xs = 
--  case unapply i xs of
--    Nothing -> fail "Deconstructor failed"
--    Just ys -> mkPrinter f ys
--mkPrinter (Alt f1 f2) a = msum [mkPrinter f1 a, mkPrinter f2 a]
