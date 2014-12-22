{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module Format.Parser.Base where

import Format.Base
import Control.Monad
import Control.Applicative
import Control.Isomorphism.Partial
import Data.HList

class ParseFormat m i where
  mkParser :: Format m i xs -> m (HList xs)

class ParseToken m i where
  parseToken :: m i

instance (ParseToken m i, Monad m, Alternative m) => ParseFormat m i where
  mkParser (Seq a b) = happend <$> mkParser a <*> mkParser b
  mkParser (CFormat i fargs) = do
      args <- mkParser fargs
      case apply i args of
        Just xs -> return xs
        Nothing -> fail "Constructor failed"
  mkParser (Alt d1 d2) = mkParser d1 <|> mkParser d2
  mkParser (Fail _) = fail "Unknown parse error"
  mkParser Token = hsingleton <$> parseToken
  mkParser (Pure hs) = pure hs
