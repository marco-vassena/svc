{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

-- A naive parser implementation

module Format.Parser.Naive (
    module Format.Parser.Base
  , parse
  , parseM
  , Parser
  ) where

import Format.Parser.Base
import Control.Applicative

newtype Parser i a = Parser { runParser :: ([i] -> [(a,[i])])}

parse :: Parser i a -> [ i ] -> [ a ]
parse p s = [x | (x, []) <- runParser p s]

parseM :: Monad m => Parser i a -> [ i ] -> m a
parseM p s = 
  case parse p s of
    [] -> fail "Parse Error"
    [x] -> return x
    _ -> fail "Ambiguous input"
    
instance ParseToken (Parser Char) Char where
  parseToken = Parser $ \xs ->
    case xs of
      [] -> []
      (x:xs) -> [(x, xs)]

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
