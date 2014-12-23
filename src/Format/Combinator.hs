{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}

-- This module provides common combinators

module Format.Combinator where

import Format.Base
import Data.HList
import Control.Applicative ((*>), pure)
import Control.Isomorphism.Partial
import qualified Control.Isomorphism.Partial as C
import Data.Type.Equality
import Debug.Trace

-- | 'between left right f' is a format in which f must occur between 
-- 'left' and 'right'
between :: Format m i '[] -> Format m i '[] -> Format m i xs -> Format m i xs
between l r p = l @> p <@ r

-- The unit format. The parser succeeds without consuming any input
-- and does not print nothing at all.
unit :: Format m i '[]
unit = Pure Nil

token :: Format m i '[i]
token = Token

match :: Eq i => i -> Format m i '[]
match x = element x <$> token

failWith :: Reify f => f xs -> Format m i xs
failWith = Fail . toSList

-------------------------------------------------------------------------------
-- Syntactic sugar operators that resemble applicative and alternative style
-- parsers.

infixr 4 <$>

(<$>) :: Iso args xs -> Format m i args -> Format m i xs
(<$>) = CFormat


infixr 3 <|>

(<|>) :: Format m i xs -> Format m i xs -> Format m i xs
(<|>) = Alt

infixr 4 <@>, <@, @>

(<@>) :: Format m i xs -> Format m i ys -> Format m i (Append xs ys)
(<@>) = Seq

(<@) :: Format m i xs -> Format m i '[] -> Format m i xs
p <@ q = 
  case rightIdentityAppend (toSList p) of
    Refl -> p <@> q

(@>) :: Format m i '[] -> Format m i ys -> Format m i ys
p @> q = 
  case leftIdentityAppend (toSList q) of
    Refl -> p <@> q

--------------------------------------------------------------------------------

-- The order is relevant: if the parser is symmetric 
many :: SList xs -> Format m i xs -> Format m i (Map [] xs)
many s f = manyEmpty <$> Pure (hsingleton []) <|> combine <$> f <@> many s f
  where manyEmpty = Iso from to (SCons SNil) (smap (const []) s)
        from      = Just . happly (unList s)
        to        = Just . hsingleton . toList s
        combine   = inverse $ unpack (mapPreservesLength s (const [])) (zipper s)

---- Let's start with the simple version of many.
many' :: SFormat m i a -> SFormat m i [a]
many' p = cons <$> p <@> many' p
       <|> nil <$> unit

-- TODO add support for arbitrary formats
some :: Format m i '[ a ] -> Format m i '[ [a] ]
some p = cons <$> (p <@> many' p )

sepBy :: Format m i '[ a ] -> Format m i '[] -> Format m i '[ [ a ] ]
sepBy p sep = cons <$> p <@> many' (sep @> p)
           <|> nil <$> unit

-- Tries each format until one succeeds.
-- The given list may not be empty.
choice :: [Format m i xs] -> Format m i xs
choice (x:xs) = foldr (<|>) (failWith x) (x:xs)
choice [] = error "Format.Combinator.choice: empty list"

count :: Int -> SFormat m i a -> SFormat m i [a]
count n f | n <= 0    = nil <$> unit
count n f | otherwise = cons <$> f <@> count (n - 1) f

optional :: SFormat m i a -> SFormat m i (Maybe a)
optional f = (just <$> f) <|> (nothing <$> unit)

(<+>) :: SFormat m i a -> SFormat m i b -> SFormat m i (Either a b)
f1 <+> f2 = (left <$> f1) <|> (right <$> f2)

-- TODO these combinators are specific for the token type
-- Possible extensions:
--   1) Extend it for any type
--   2) Extend it for any format (any xs)
oneOf :: Eq i => [ i ] -> Format m i '[ i ]
oneOf xs = satisfy (`elem` xs)

noneOf :: Eq i => [ i ] -> Format m i '[ i ]
noneOf xs = satisfy (not . (`elem` xs))

-- TODO add anyOf

satisfy :: (i -> Bool) -> Format m i '[ i ]
satisfy p = subset (SCons SNil) (happly p) <$> token

-- | The `chainl1` combinator is used to parse a
-- left-associative chain of infix operators. 
chainl1 :: SFormat m i a -> SFormat m i b -> Iso '[a, b, a] '[a] -> SFormat m i a
chainl1 arg op f = C.foldl s f <$> arg <@> many s (op <@> arg)
  where s = SCons (SCons SNil)
