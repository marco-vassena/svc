{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module Format.Parser.Generic where

import Control.Monad
import Control.Applicative
import Control.Isomorphism.Partial
import Data.HList
import Format.Base
import Format.Parser.Base

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
  mkParser (Bind _ f k) = do
    hs1 <- mkParser f 
    hs2 <- mkParser (k hs1)
    return (happend hs1 hs2)
