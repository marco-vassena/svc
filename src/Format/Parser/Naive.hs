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
import Format.Parser.Base
import Format.Parser.GParser
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
 
--------------------------------------------------------------------------------
-- If the Parser is an instance of Alternative-Monad this is 
-- the only instance needed to use the Format framework.
instance ParseSatisfy (Parser i) i where
  parseSatisfy = pSatisfy

instance ParseHelp (Parser i)

-- Returns the next token in the stream.
nextToken :: Parser i i
nextToken = Parser $ \xs ->
    case xs of
      [] -> []
      (x:xs) -> [(x, xs)]

-- Returns the next token in the stram only if it satisfy the predicate.
pSatisfy :: (i -> Bool) -> Parser i i
pSatisfy p = do 
  c <- nextToken
  if p c then pure c else empty
