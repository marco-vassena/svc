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


-- | A single format that targets 'Int'.
int :: StreamChar i => Format i '[ Int ]
int = Target

-- | A single format that targets 'Char'.
char :: StreamChar i => Format i '[ Char ]
char = Target

-- | A format that encodes the presence of the given value
tag :: (Match i a, Printable i a) => a -> Format i '[]
tag = Meta

-- | 'between left right f' is a format in which f must occur between 
-- 'left' and 'right'
between :: Format i '[] -> Format i '[] -> Format i xs -> Format i xs
between l r p = l @> p <@ r

-- The unit format. The parser succeeds without consuming any input
-- and does not print nothing at all.
unit :: StreamChar i => Format i '[]
unit = Meta ()

-- | It represents a set of characters to be matched.
data AnyOf a = AnyOf a [a]

anyOf :: (Stream i Identity a, Match i a, Printable i a) => [a] -> Format i '[]
anyOf (c:cs) = Meta (AnyOf c cs)
anyOf [] = error "Format.Char.anyOf : empty list"

instance Printable i a => Printable i (AnyOf a) where
  printer (AnyOf c cs) = printer c

instance (Stream i Identity a, Match i a) => Match i (AnyOf a) where
  match a@(AnyOf c cs) = P.choice (map match(c:cs)) *> pure a

-- TODO: add format for failure

-------------------------------------------------------------------------------
-- Syntactic sugar operators that resemble applicative and alternative style
-- parsers.

infixr 4 <$>

(<$>) :: Iso args xs -> Format i args -> Format i xs
(<$>) = CFormat


infixr 3 <|>

(<|>) :: Format i xs -> Format i xs -> Format i xs
(<|>) = Alt


infixr 4 <@>, <@, @>

(<@>) :: Format i xs -> Format i ys -> Format i (Append xs ys)
(<@>) = Seq

(<@) :: Format i xs -> Format i '[] -> Format i xs
(<@) = SkipR 

(@>) :: Format i '[] -> Format i ys -> Format i ys
(@>) = SkipL 

--------------------------------------------------------------------------------

many :: StreamChar i => Format i xs -> Format i (Map [] xs)
many p = 
  case toSList p of
    SCons SNil -> cons <$> p <@> many p
                  <|> nil <$> unit
    _ -> Many p

-- TODO add support for arbitrary formats
some :: StreamChar i => Format i '[ a ]-> Format i '[ [a] ]
some p = cons <$> (p <@> many p )

sepBy :: StreamChar i => 
            Format i '[ a ] -> Format i '[] -> Format i '[ [ a ] ]
sepBy p sep = cons <$> p <@> many (sep @> p)
           <|> nil  <$> unit

-- Tries each format until one succeeds.
-- The given list must be non empty
choice :: [Format i xs] -> Format i xs
choice (x:xs) = foldr (<|>) x xs
choice [] = error "Format.Combinator.choice: empty list"

count :: StreamChar i => Int -> SFormat i a -> SFormat i [a]
count n f | n <= 0    = nil <$> unit
count n f | otherwise = cons <$> f <@> count (n - 1) f

optional :: StreamChar i => SFormat i a -> SFormat i (Maybe a)
optional f = (just <$> f) <|> (nothing <$> unit)

(<+>) :: SFormat i a -> SFormat i b -> SFormat i (Either a b)
f1 <+> f2 = (left <$> f1) <|> (right <$> f2)

-- Specialized version of 'Satisfy' for single formats
satisfy :: (a -> Bool) -> SFormat i a -> SFormat i a
satisfy p = Satisfy (\(Cons x _) -> p x)

oneOf :: (Parsable i a, Printable i a, Eq a) => [ a ] -> Format i '[ a ]
oneOf xs = satisfy (`elem` xs) Target

noneOf :: (Parsable i a, Printable i a, Eq a) => [ a ] -> Format i '[ a ]
noneOf xs = satisfy (not . (`elem` xs)) Target

-- | The `chainl1` combinator is used to parse a
-- left-associative chain of infix operators. 
chainl1 :: StreamChar i => SFormat i a -> SFormat i b -> Iso '[a, b, a] '[a] -> SFormat i a
chainl1 arg op f = C.foldl (SCons (SCons SNil)) f <$> arg <@> many (op <@> arg)
