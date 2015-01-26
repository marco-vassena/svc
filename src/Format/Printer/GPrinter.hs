{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Format.Printer.GPrinter where

import Format.Base hiding ((<$>), (<*>), (<|>), pure, fail)
import Format.Printer.Base
import Data.Monoid
import Data.HList
import Control.Applicative
import Control.Isomorphism.Partial

-- Relates the token type with the stream type.
class PrintToken m i s where
  printToken :: i -> m s

instance (Show i, PrintToken m i s, Monad m) => PrintWith s m i (Satisfy (PrintWith s)) where
  mkPrinter' (Satisfy p) (Cons i _) | p i       = printToken i
  mkPrinter' (Satisfy p) (Cons i _) | otherwise = fail $ show i ++ " : predicate not satisfied" 

instance (Applicative m, Monoid s) => PrintWith s m i (Seq (PrintWith s)) where
  mkPrinter' (Seq f1 f2) hs = mappend <$> mkPrinter' f1 hs1 <*> mkPrinter' f2 hs2
    where (hs1, hs2) = split (toSList f1) (toSList f2) hs

instance (Alternative m) => PrintWith s m i (Alt (PrintWith s)) where
  mkPrinter' (Alt f1 f2) hs = mkPrinter' f1 hs <|> mkPrinter' f2 hs

instance PrintWith s m i (Format (PrintWith s)) where
  mkPrinter' (Format f) = mkPrinter' f

-- TODO
-- It seems that in order to deal with partial isomorphisms we
-- need m to be at least Alternative (empty) or a Monad (fail)
-- How can we relax this constraint?
instance Monad m => PrintWith s m i (FMap (PrintWith s)) where
  mkPrinter' (FMap i f) xs = do 
    case unapply i xs of
      Just ys -> mkPrinter' f ys
      Nothing -> fail "Deconstructor failed"

instance (Monoid s, Applicative m) => PrintWith s m i (Pure (PrintWith s)) where
  mkPrinter' (Pure hs) hs' = pure mempty

instance (Monoid s, Applicative m) => PrintWith s m i (Bind (PrintWith s)) where
  mkPrinter' (Bind s f1 k) hs = mappend <$> mkPrinter' f1 hs1 <*> mkPrinter' f2 hs2
    where (hs1, hs2) = split (toSList f1) s hs
          f2 = k hs1
