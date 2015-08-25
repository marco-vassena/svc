{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

module Format.Parser.GParser where

import Format.Syntax hiding ((<$>), (<*>), (<|>), pure, fail, (>>=), empty, return)
import Format.Parser.Base
import Data.TypeList.HList
import Control.Applicative
import Control.Isomorphism.Partial

import Data.Proxy

class ParseSatisfy m i where
  parseSatisfy :: (i -> Bool) -> m i

class ParseHelp m where
  parseHelp :: m a -> String -> m a
  parseHelp = const

class ParseTry m where
  parseTry :: m a -> m a
  parseTry = id

instance Applicative m => ParseWith m i (ApplicativeS ParseWith) where
  mkParser' (Pure hs) = pure hs
  mkParser' (Star f1 f2) = happend <$> mkParser' f1 <*> mkParser' f2

instance (Functor m) => ParseWith m i (FunctorS ParseWith) where
  mkParser' (FMap i f) = apply i <$> mkParser' f 

instance Alternative m => ParseWith m i (AlternativeS ParseWith) where
  mkParser' (Empty _) = empty
  mkParser' (Choice f1 f2) = mkParser' f1 <|> mkParser' f2

instance ParseWith m i (Format ParseWith) where
  mkParser' (Format f) = mkParser' f

instance Monad m => ParseWith m i (MonadS ParseWith) where
  mkParser' (Return hs) = return hs
  mkParser' (Fail _ s) = fail s
  mkParser' (Bind _ f k) = do 
    hs1 <- mkParser' f 
    hs2 <- mkParser' (k hs1)
    return (happend hs1 hs2)

instance (Functor m, ParseSatisfy m i) => ParseWith m i (Satisfy ParseWith) where
  mkParser' (Satisfy p) = hsingleton <$> parseSatisfy p

instance ParseHelp m => ParseWith m i (Help ParseWith) where
  mkParser' (Help f msg) = parseHelp (mkParser' f) msg

instance ParseTry m => ParseWith m i (Try ParseWith) where
  mkParser' (Try f) = parseTry (mkParser' f)
