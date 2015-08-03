{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Format.Printer.GPrinter where

import Format.Syntax hiding ((<$>), (<*>), (<|>), pure, fail, (>>=), empty)
import Format.Printer.Base
import Data.Monoid
import Data.TypeList.HList
import Control.Applicative
import Control.Isomorphism.Partial

-- Relates the token type with the stream type.
class PrintToken m i s where
  printToken :: i -> m s

class PrintHelp m where
  printHelp :: m a -> String -> m a
  printHelp = const

class PrintTry m where
  printTry :: m a -> m a
  printTry = id

instance (Show i, PrintToken m i s, Monad m) => PrintWith s m i (Satisfy (PrintWith s)) where
  mkPrinter' (Satisfy p) (Cons i _) | p i       = printToken i
  mkPrinter' (Satisfy p) (Cons i _) | otherwise = fail $ show i ++ " : predicate not satisfied" 

instance (Applicative m, Monoid s) => PrintWith s m i (Seq (PrintWith s)) where
  mkPrinter' (Seq f1 f2) hs = mappend <$> mkPrinter' f1 hs1 <*> mkPrinter' f2 hs2
    where (hs1, hs2) = split (toSList f1) (toSList f2) hs

instance Alternative m => PrintWith s m i (Alt (PrintWith s)) where
  mkPrinter' (Alt f1 f2) hs = mkPrinter' f1 hs <|> mkPrinter' f2 hs

instance Alternative m => PrintWith s m i (Empty (PrintWith s)) where
  mkPrinter' (Empty _) _ = empty

instance PrintWith s m i (Format (PrintWith s)) where
  mkPrinter' (Format f) = mkPrinter' f

-- TODO
-- It seems that in order to deal with partial isomorphisms we
-- need m to be at least Alternative (empty) or a Monad (fail)
-- How can we relax this constraint?
instance Alternative m => PrintWith s m i (FMap (PrintWith s)) where
  mkPrinter' (FMap i f) hs =
    case unapply i hs  of 
      Just ys -> mkPrinter' f ys
      Nothing -> empty

instance (Monoid s, Applicative m) => PrintWith s m i (Pure (PrintWith s)) where
  mkPrinter' (Pure hs) hs' = pure mempty

instance (Monoid s, Applicative m) => PrintWith s m i (Bind (PrintWith s)) where
  mkPrinter' (Bind s f1 k) hs = mappend <$> mkPrinter' f1 hs1 <*> mkPrinter' f2 hs2
    where (hs1, hs2) = split (toSList f1) s hs
          f2 = k hs1

instance PrintHelp m => PrintWith s m i (Help (PrintWith s)) where
  mkPrinter' (Help f msg) hs = printHelp (mkPrinter' f hs) msg

instance PrintTry m => PrintWith s m i (Try (PrintWith s)) where
  mkPrinter' (Try f) hs = printTry (mkPrinter' f hs)
