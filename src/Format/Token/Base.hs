{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}

-- Generic token-based combinators.

module Format.Token.Base where

import Prelude hiding (takeWhile)
import Data.TypeList.HList

import Format.Syntax
import Format.Combinator

import Control.Isomorphism.Partial 

type MatchC c m i = (Eq i, Show i, 
                     SatisfyC    c m i,
                     FunctorC    c m i,
                     Use Help    c m i)

-- | @match x@ is a format that expect the token @x@.
match :: MatchC c m i => i -> Format c m i '[]
match x = ignore (hsingleton x) <$> satisfy (x ==) <?> show x

-- | This format accepts any token.
token :: MatchC c m i => Format c m i '[i]
token = satisfy (const True)

-- | @tokens xs@ is a format that expects the sequence of tokens @xs@ as output.
tokens :: (MatchC c m i, AlternativeC c m i) => [i] -> Format c m i '[]
tokens xs = go xs <?> show xs
  where go [] = identity SNil <$> unit -- Just unit
        go (x:xs) = identity SNil <$> match x <*> (go xs) -- TODO you can remove identity from here

-- | @oneOf xs@ is a format that expects a token among those in @xs@.
oneOf :: (Eq i, SatisfyC c m i) => [ i ] -> Format c m i '[ i ]
oneOf xs = satisfy (`elem` xs)

-- | @noneOf xs@ is a format that expects a token that is /not/ among those in @xs@.
noneOf :: (Eq i, SatisfyC c m i) => [ i ] -> Format c m i '[ i ]
noneOf xs = satisfy (not . (`elem` xs))
