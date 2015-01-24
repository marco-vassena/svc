{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}

module Format.Token.Base where

import Prelude hiding (takeWhile)
import Data.HList

import Format.Base
import Format.Combinator

import Control.Isomorphism.Partial 

type SatisfyC c m i = (Use Satisfy c m i '[i], 
                       Use FMap   c m i '[i], 
                       Use Format c m i '[i])

type MatchC c m i = (Use FMap   c m i '[], 
                     Use Format c m i '[i],
                     Use Token  c m i '[i],
                     Eq i)

type TokensC c m i = (MatchC c m i,
                      Use Pure   c m i '[], 
                      Use Format c m i '[], 
                      Use Seq    c m i '[])

-- Used when many is applied to a format of that returns the token type
type ManyToken c m i = ManyC c m i '[i] 
                     
match :: MatchC c m i => i -> Format c m i '[]
match x = element x <$> token

tokens :: TokensC c m i => [i] -> Format c m i '[]
tokens [] = identity SNil <$> unit
tokens (x:xs) = identity SNil <$> match x <*> (tokens xs)

oneOf :: (SatisfyC c m i, Eq i) => [ i ] -> Format c m i '[ i ]
oneOf xs = satisfy (`elem` xs)

noneOf :: (SatisfyC c m i, Eq i) => [ i ] -> Format c m i '[ i ]
noneOf xs = satisfy (not . (`elem` xs))

-- TODO Add anyOf
