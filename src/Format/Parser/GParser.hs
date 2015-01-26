{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

module Format.Parser.GParser where

import Format.Syntax hiding ((<$>), (<*>), (<|>), pure, fail)
import Format.Parser.Base
import Data.HList
import Control.Applicative
import Control.Isomorphism.Partial

class ParseSatisfy m i where
  parseSatisfy :: (i -> Bool) -> m i

instance Applicative m => ParseWith m i (Seq ParseWith) where
  mkParser' (Seq f1 f2) = happend <$> mkParser' f1 <*> mkParser' f2

-- TODO
-- It seems that in order to deal with partial isomorphisms we
-- need m to be at least Alternative (empty) or a Monad (fail)
-- How can we relax this constraint?
instance (Alternative m, Monad m) => ParseWith m i (FMap ParseWith) where
  mkParser' (FMap i f) = do 
    args <- mkParser' f
    case apply i args of
      Just xs -> pure xs
      Nothing -> empty


instance Alternative m => ParseWith m i (Alt ParseWith) where
  mkParser' (Alt f1 f2) = mkParser' f1 <|> mkParser' f2

instance ParseWith m i (Format ParseWith) where
  mkParser' (Format f) = mkParser' f

instance Alternative m => ParseWith m i (Pure ParseWith) where
  mkParser' (Pure hs) = pure hs

instance Monad m => ParseWith m i (Bind ParseWith) where
  mkParser' (Bind _ f k) = do 
    hs1 <- mkParser' f 
    hs2 <- mkParser' (k hs1)
    return (happend hs1 hs2)

instance (Functor m, ParseSatisfy m i) => ParseWith m i (Satisfy ParseWith) where
  mkParser' (Satisfy p) = hsingleton <$> parseSatisfy p
