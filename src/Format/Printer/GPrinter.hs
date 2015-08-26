{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

-- | This module gives generic instances for PrintWith,
-- for printers instance of Functor, Applicative, Alternative and Monad.
-- An explicit instance for @PrintToken@, and the automatically inferred 
-- instances for all the other descriptors should be sufficient
-- to embedd a printing library as the backward semantics of a
-- format descriptor.


module Format.Printer.GPrinter where

import Format.Syntax hiding ((<$>), (<*>), (<|>), pure, fail, (>>=), empty, return)
import Format.Printer.Base
import Data.Monoid
import Data.TypeList.HList
import Control.Applicative
import Control.Isomorphism.Partial

--------------------------------------------------------------------------------
-- These classes represents hooks for library-specific primitives.

-- Relates the token type with the stream type.
class PrintToken m i s where
  printToken :: i -> m s

class PrintHelp m where
  printHelp :: m a -> String -> m a
  printHelp = const

class PrintTry m where
  printTry :: m a -> m a
  printTry = id

--------------------------------------------------------------------------------

instance Alternative m => PrintWith s m i (FunctorS (PrintWith s)) where
  mkPrinter' (FMap i f) hs =
    case unapply i hs  of 
      Just ys -> mkPrinter' f ys
      Nothing -> empty

instance (Applicative m, Monoid s) => PrintWith s m i (ApplicativeS (PrintWith s)) where
  mkPrinter' (Pure hs) hs' = pure mempty
  mkPrinter' (Star f1 f2) hs = mappend <$> mkPrinter' f1 hs1 <*> mkPrinter' f2 hs2
    where (hs1, hs2) = split (toSList f1) (toSList f2) hs

instance Alternative m => PrintWith s m i (AlternativeS (PrintWith s)) where
  mkPrinter' (Empty _) _ = empty
  mkPrinter' (Choice f1 f2) hs = mkPrinter' f1 hs <|> mkPrinter' f2 hs

instance (Monoid s, Monad m) => PrintWith s m i (MonadS (PrintWith s)) where
  mkPrinter' (Fail _ s) _ = fail s
  mkPrinter' (Return _) _ = return mempty
  mkPrinter' (Bind s f1 k) hs = do
      s1 <- mkPrinter' f1 hs1 
      s2 <- mkPrinter' f2 hs2
      return (mappend s1 s2)
    where (hs1, hs2) = split (toSList f1) s hs
          f2 = k hs1

instance PrintWith s m i (Format (PrintWith s)) where
  mkPrinter' (Format f) = mkPrinter' f

--------------------------------------------------------------------------------
-- Automatic instances derived assuming instances for the hooks in the context

instance (Show i, PrintToken m i s, Monad m) => PrintWith s m i (Satisfy (PrintWith s)) where
  mkPrinter' (Satisfy p) (Cons i _) | p i       = printToken i
  mkPrinter' (Satisfy p) (Cons i _) | otherwise = fail $ show i ++ " : predicate not satisfied" 

instance PrintHelp m => PrintWith s m i (Help (PrintWith s)) where
  mkPrinter' (Help f msg) hs = printHelp (mkPrinter' f hs) msg

instance PrintTry m => PrintWith s m i (Try (PrintWith s)) where
  mkPrinter' (Try f) hs = printTry (mkPrinter' f hs)
