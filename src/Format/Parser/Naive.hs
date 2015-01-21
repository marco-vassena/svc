{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE UndecidableInstances #-}

-- A naive parser implementation

module Format.Parser.Naive (
    module Format.Parser.Base
  , parse
  , parseM
  , Parser
  ) where

import Data.HList
import Format.Base
import Format.Parser.Base
import Format.Parser.Generic
import Control.Applicative
import Control.Isomorphism.Partial

newtype Parser i a = Parser { runParser :: ([i] -> [(a,[i])])}

parse :: Parser i a -> [ i ] -> [ a ]
parse p s = [x | (x, []) <- runParser p s]

parseM :: Monad m => Parser i a -> [ i ] -> m a
parseM p s = 
  case parse p s of
    [] -> fail "Parse Error"
    [x] -> return x
    _ -> fail "Ambiguous input"
 

nextToken :: Parser i i
nextToken = Parser $ \xs ->
    case xs of
      [] -> []
      (x:xs) -> [(x, xs)]

   
instance ParseToken (Parser Char) Char where
  parseToken = nextToken

instance Functor (Parser i) where
  fmap f p = Parser $ \s -> [ (f a, s') | (a, s') <- runParser p s ]
      
instance Applicative (Parser i) where
  pure x = Parser (\s -> [(x,s)])
  p <*> q = Parser $ \s -> [(f a, s'') | (f, s' ) <- runParser p s, 
                                         (a, s'') <- runParser q s']

instance Alternative (Parser i) where
  empty = Parser (const [])
  p <|> q = Parser $ \s -> runParser p s ++ runParser q s

instance Monad (Parser i) where
  return = pure
  p >>= f = Parser $ \s -> concat [runParser (f a) s' | (a, s') <- runParser p s]
  fail _ = Parser $ const []

instance ParseWith (Parser i) i '[ i ] (Token' c) where
  mkParser' _ = hsingleton <$> nextToken
 
instance ParseWith (Parser i) i zs (Seq' ParseWith) where
  mkParser' (Seq' f1 f2) = happend <$> mkParser' f1 <*> mkParser' f2

instance ParseWith (Parser i) i xs (CFormat' ParseWith) where
  mkParser' (CFormat' i f) = do 
    args <- mkParser' f
    case apply i args of
      Just xs -> return xs
      Nothing -> fail "Constructor failed"

instance ParseWith (Parser i) i xs (Alt' ParseWith) where
  mkParser' (Alt' f1 f2) = mkParser' f1 <|> mkParser' f2
