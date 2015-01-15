{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}

module Format.Parser.Parsec where

import Control.Isomorphism.Partial
import Control.Applicative ((<$>), (<*>), pure)
import Data.HList
import Format.Base
import Format.Parser.Base
import Text.Parsec

instance (Stream s m t, Show t) => ParseFormat (ParsecT s u m) t where
  mkParser (Seq a b) = happend <$> mkParser a <*> mkParser b
  mkParser (CFormat i fargs) = try $ do
      args <- mkParser fargs
      case apply i args of
        Just xs -> return xs
        Nothing -> fail "Constructor failed"
  mkParser (Alt d1 d2) = try (mkParser d1) <|> mkParser d2
  mkParser (Fail _) = fail "Unknown parse error"
  mkParser Token = hsingleton <$> anyToken
  mkParser (Pure hs) = pure hs
  mkParser (Bind _ f k) = do
    hs1 <- mkParser f 
    hs2 <- mkParser (k hs1)
    return (happend hs1 hs2)


