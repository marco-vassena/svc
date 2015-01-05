{-# LANGUAGE DataKinds #-}

module Format.Token.Base where

import Prelude hiding (takeWhile)
import Data.HList

import Format.Base
import Format.Combinator

import Control.Isomorphism.Partial hiding (takeWhile, takeWhile1)
import qualified Control.Isomorphism.Partial as C

token :: Format m i '[ i ]
token = Token

match :: Eq i => i -> Format m i '[]
match x = element x <$> token

oneOf :: Eq i => [ i ] -> Format m i '[ i ]
oneOf xs = satisfy (`elem` xs)

noneOf :: Eq i => [ i ] -> Format m i '[ i ]
noneOf xs = satisfy (not . (`elem` xs))

-- TODO Add anyOf

takeWhile :: (i -> Bool) -> Format m i '[ [i] ]
takeWhile p = C.takeWhile (SCons SNil) (happly p) <$> many token

takeWhile1 :: (i -> Bool) -> Format m i '[ [i] ]
takeWhile1 p = C.takeWhile1 (SCons SNil) (happly p) <$> some token

--takeWhile :: (i -> Bool) -> Format m i '[ [i] ]
--takeWhile p = takeWhile1 p
--        <|> inverse (allEmpty (SCons SNil)) <$> unit
--
---- takeWhile1 :: SList xs -> Format m i xs -> Format m i (Map [] xs)
--takeWhile1 :: (i -> Bool) -> Format m i '[ [i] ]
--takeWhile1 p = inverse (combine (SCons SNil)) <$> (satisfy p) <@> takeWhile p

satisfy :: (i -> Bool) -> Format m i '[ i ]
satisfy p = subset (SCons SNil) (happly p) <$> token
