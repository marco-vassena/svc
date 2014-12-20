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
import Data.Functor.Identity (Identity)
import Text.Parsec.Char hiding (satisfy)
import Text.Parsec.Combinator hiding ((<|>), count, choice)
import qualified Text.Parsec.Combinator as P
import Text.Parsec.Prim hiding ((<|>), many)
import Data.HList
import Control.Applicative ((*>), pure)
import Control.Isomorphism.Partial
import qualified Control.Isomorphism.Partial as C
import Data.Type.Equality

-- | 'between left right f' is a format in which f must occur between 
-- 'left' and 'right'
between :: Format m i '[] -> Format m i '[] -> Format m i xs -> Format m i xs
between l r p = l @> p <@ r

-- The unit format. The parser succeeds without consuming any input
-- and does not print nothing at all.
unit :: Format m i '[]
unit = Match Nil 

token :: Format m i '[i]
token = Token

match :: a -> Format m i '[]
match = Match . hsingleton

-- | It represents a set of characters to be matched.
data AnyOf a = AnyOf a [a]

anyOf :: [a] -> Format m i '[]
anyOf (c:cs) = undefined -- (AnyOf c cs)
anyOf [] = error "Format.anyOf : empty list"

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

many :: Format m i xs -> Format m i (Map [] xs)
many p = undefined
--  case toSList p of
--    SCons SNil -> cons <$> p <@> many p
--                  <|> nil <$> unit
--    _ -> Many p

-- TODO add support for arbitrary formats
some :: Format m i '[ a ] -> Format m i '[ [a] ]
some p = cons <$> (p <@> many p )

sepBy :: Format m i '[ a ] -> Format m i '[] -> Format m i '[ [ a ] ]
sepBy p sep = cons <$> p <@> many (sep @> p)
           <|> nil  <$> unit

-- Tries each format until one succeeds.
-- The given list must be non empty
choice :: [Format m i xs] -> Format m i xs
choice (x:xs) = foldr (<|>) x xs
choice [] = error "Format.Combinator.choice: empty list"

count :: Int -> SFormat m i a -> SFormat m i [a]
count n f | n <= 0    = nil <$> unit
count n f | otherwise = cons <$> f <@> count (n - 1) f

optional :: SFormat m i a -> SFormat m i (Maybe a)
optional f = (just <$> f) <|> (nothing <$> unit)

(<+>) :: SFormat m i a -> SFormat m i b -> SFormat m i (Either a b)
f1 <+> f2 = (left <$> f1) <|> (right <$> f2)

oneOf :: Eq a => [ a ] -> Format m i '[ a ]
oneOf xs = undefined

noneOf :: Eq a => [ a ] -> Format m i '[ a ]
noneOf xs = undefined

satisfy :: (a -> Bool) -> Format m i '[ a ] -> Format m i '[ a ]
satisfy = undefined

-- | The `chainl1` combinator is used to parse a
-- left-associative chain of infix operators. 
chainl1 :: SFormat m i a -> SFormat m i b -> Iso '[a, b, a] '[a] -> SFormat m i a
chainl1 arg op f = C.foldl (SCons (SCons SNil)) f <$> arg <@> many (op <@> arg)
