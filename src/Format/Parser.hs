{-# LANGUAGE MultiParamTypeClasses #-}

module Format.Parser where

import Format.Base
import Data.HList

class ParseFormat m i where
  parseToken :: m i
  mkParser :: Format m i xs -> m (HList xs)

--mkParser :: Format m i xs -> m (HList xs)
--mkParser (Seq a b) = happend <$> mkParser a <*> mkParser b
--mkParser (CFormat i fargs) = try $ do
--  args <- mkParser fargs
--  case apply i args of
--    Just xs -> return xs
--    Nothing -> fail "Construcor failed"
--mkParser (Alt d1 d2) = mkParser d1 <|> mkParser d2

