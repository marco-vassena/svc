{-# LANGUAGE DataKinds #-}

module Format.Token.Base where

import Prelude hiding (takeWhile)
import Data.HList

import Format.Base
import Format.Combinator

import Control.Isomorphism.Partial 

token :: Format m i '[ i ]
token = Token

match :: Eq i => i -> Format m i '[]
match x = element x <$> token

oneOf :: Eq i => [ i ] -> Format m i '[ i ]
oneOf xs = satisfy (`elem` xs)

noneOf :: Eq i => [ i ] -> Format m i '[ i ]
noneOf xs = satisfy (not . (`elem` xs))

-- TODO Add anyOf

satisfy :: (i -> Bool) -> Format m i '[ i ]
satisfy p = subset (SCons SNil) (happly p) <$> token
