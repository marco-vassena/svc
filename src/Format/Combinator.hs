{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}

-- This module provides common combinators

module Format.Combinator where

import Format.Base
import Data.Functor.Identity (Identity)
import Text.Parsec.Char hiding (satisfy)
import Text.Parsec.Combinator hiding ((<|>), count)
import Text.Parsec.Prim hiding ((<|>), many)
import Format.HList

-- | A single format that targets 'Int'.
int :: StreamChar i => Format i '[ Int ]
int = Target

-- | A single format that targets 'Char'.
char :: StreamChar i => Format i '[ Char ]
char = Target

-- | 'between left right f' is a format in which f must occur between 
-- 'left' and 'right'
between :: Format i '[] -> Format i '[] -> Format i xs -> Format i xs
between l r p = l @> p <@ r

-- The unit format. The parser succeeds without consuming any input
-- and does not print nothing at all.
unit :: StreamChar i => Format i '[]
unit = Meta ()

-- TODO: add format for failure

-------------------------------------------------------------------------------
-- Syntactic sugar operators that resemble applicative and alternative style
-- parsers.

infixr 4 <$>

(<$>) :: Proj a args => (HList args -> a) -> Format i args -> SFormat i a
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

-- Requires IncoherentInstances :(
--(<+>) :: SFormat i a -> SFormat i b -> SFormat i (Either a b)
--f1 <+> f2 = (left <$> f1) <|> (right <$> f2)

-- Specialized version of 'Satisfy' for single formats
satisfy :: (a -> Bool) -> SFormat i a -> SFormat i a
satisfy p = Satisfy (\(Cons x _) -> p x)

oneOf :: (Parsable i a, Printable i a, Eq a) => [ a ] -> Format i '[ a ]
oneOf xs = satisfy (`elem` xs) Target

noneOf :: (Parsable i a, Printable i a, Eq a) => [ a ] -> Format i '[ a ]
noneOf xs = satisfy (not . (`elem` xs)) Target

-- These instances can be automatically derived using TH
instance Proj [ a ] '[] where
  proj [] = Just Nil
  proj _ = Nothing

instance Proj [ a ] '[a , [a]] where
  proj (x:xs) = Just $ Cons x (Cons xs Nil)
  proj _ = Nothing

instance Proj (Maybe a) '[ a ] where
  proj (Just x) = Just (Cons x Nil)
  proj _ = Nothing

instance Proj (Maybe a) '[] where
  proj Nothing = Just Nil
  proj _ = Nothing

--instance Proj (Either a b) '[ a ] where
--  proj (Left x) = Just (Cons x Nil)
--
--instance Proj (Either a b) '[ b ] where
--  proj (Right y) = Just (Cons y Nil)
--

-- Constructors curried to work with list
nil :: HList '[] -> [ a ]
nil Nil = []

cons :: HList '[a , [a]] -> [ a ]
cons (Cons x (Cons xs Nil)) = x:xs

-- Constructors curried to work with maybe values
just :: HList '[ a ] -> Maybe a
just (Cons x Nil) = Just x

nothing :: HList '[] -> Maybe a
nothing Nil = Nothing

-- Constructors curried to work with either vaues
left :: HList '[ a ] -> Either a b
left (Cons x Nil) = Left x

right :: HList '[ b ] -> Either a b
right (Cons y Nil) = Right y
