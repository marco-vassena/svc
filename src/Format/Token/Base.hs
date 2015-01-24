{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}

module Format.Token.Base where

import Prelude hiding (takeWhile)
import Data.HList

import Format.Base
import Format.Combinator

import Control.Isomorphism.Partial 

match :: (ApplicativeC c m i, Use Token c m i,  Eq i) => i -> Format c m i '[]
match x = element x <$> token     -- TODO rewrite in terms of satisfy

tokens :: (ApplicativeC c m i, Use Token c m i, Eq i) => [i] -> Format c m i '[]
tokens [] = identity SNil <$> unit
tokens (x:xs) = identity SNil <$> match x <*> (tokens xs)

oneOf :: (Eq i, Use Satisfy c m i) => [ i ] -> Format c m i '[ i ]
oneOf xs = satisfy (`elem` xs)

noneOf :: (Eq i, Use Satisfy c m i) => [ i ] -> Format c m i '[ i ]
noneOf xs = satisfy (not . (`elem` xs))

-- TODO Add anyOf
