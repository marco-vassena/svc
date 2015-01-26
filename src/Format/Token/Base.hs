{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}

module Format.Token.Base where

import Prelude hiding (takeWhile)
import Data.HList

import Format.Syntax
import Format.Combinator

import Control.Isomorphism.Partial 

type MatchC c m i = (Eq i, Show i, 
                     Use Format  c m i, 
                     Use Satisfy c m i, 
                     Use FMap    c m i, 
                     Use Help    c m i)

match :: MatchC c m i => i -> Format c m i '[]
match x = ignore (hsingleton x) <$> satisfy (x ==) <?> show x

token :: Use Satisfy c m i => Format c m i '[i]
token = satisfy (const True)

tokens :: (MatchC c m i, AlternativeC c m i) => [i] -> Format c m i '[]
tokens xs = go xs <?> show xs
  where go [] = identity SNil <$> unit
        go (x:xs) = identity SNil <$> match x <*> (go xs)

oneOf :: (Eq i, Use Satisfy c m i) => [ i ] -> Format c m i '[ i ]
oneOf xs = satisfy (`elem` xs)

noneOf :: (Eq i, Use Satisfy c m i) => [ i ] -> Format c m i '[ i ]
noneOf xs = satisfy (not . (`elem` xs))

-- TODO Add anyOf
