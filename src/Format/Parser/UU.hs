{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Format.Parser.UU where

import Control.Isomorphism.Partial
import Data.ListLike
import Data.HList
import Format.Base
import Format.Parser
import Text.ParserCombinators.UU.BasicInstances
import Text.ParserCombinators.UU.Core hiding (Fail)

instance (IsLocationUpdatedBy loc Char, ListLike state Char) 
  => ParseFormat (P (Str Char state loc)) Char where
  mkParser (Seq a b) = happend <$> mkParser a <*> mkParser b
  mkParser (CFormat i fargs) = do
      args <- mkParser fargs
      case apply i args of
        Just xs -> return xs
        Nothing -> fail "Constructor failed"
  mkParser (Alt d1 d2) = mkParser d1 <|> mkParser d2
  mkParser (Fail _) = fail "Unknown parse error"
  mkParser Token = hsingleton <$> pRange (minBound, maxBound)
  mkParser (Pure hs) = pure hs
  mkParser (Bind _ f k) = addLength 100 $ do
    hs1 <- mkParser f 
    hs2 <- mkParser (k hs1)
    return (happend hs1 hs2)
