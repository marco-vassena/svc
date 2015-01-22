{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}

module Format.Token.Base where

import Prelude hiding (takeWhile)
import Data.HList

import Format.Base
import Format.Combinator

import Control.Isomorphism.Partial 

type SatisfyC c m i = (Use Token  c m i '[i], 
                       Use FMap   c m i '[i], 
                       Use Format c m i '[i])

type MatchC c m i = (Use FMap   c m i '[], 
                     Use Format c m i '[i],
                     Use Token  c m i '[i],
                     Eq i)

match :: MatchC c m i => i -> Format c m i '[]
match x = element x <$> token

oneOf :: (SatisfyC c m i, Eq i) => [ i ] -> Format c m i '[ i ]
oneOf xs = satisfy (`elem` xs)

noneOf :: (SatisfyC c m i, Eq i) => [ i ] -> Format c m i '[ i ]
noneOf xs = satisfy (not . (`elem` xs))

-- TODO Add anyOf

satisfy :: SatisfyC c m i => (i -> Bool) -> Format c m i '[ i ]
satisfy p = subset (SCons SNil) (happly p) <$> token
