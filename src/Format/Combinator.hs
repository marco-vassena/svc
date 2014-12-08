{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

-- This module provides common combinators

module Format.Combinator where

import Format.Base
import Data.Functor.Identity (Identity)
import Text.Parsec.Char
import Text.Parsec.Combinator hiding ((<|>), count)
import Text.Parsec.Prim hiding ((<|>), many)
import Format.HList

int :: (StringLike i, Stream i Identity Char) => Format i '[ Int ]
int = Target

char :: (StringLike i, Stream i Identity Char) => Format i '[ Char ]
char = Target

between :: (Fill l, Fill r) => Format i l -> Format i xs -> Format i r -> Format i xs
between l p r = l @> p <@ r

-- The unit format. The parser succeeds without consuming any input
-- and does not print nothing at all.
unit :: (Stream i Identity Char, StringLike i) => Format i '[]
unit = Meta ()

-- TODO: add format for failure

--------------------------------------------------------------------------------
-- Combinators for SFormat
--------------------------------------------------------------------------------

-- TODO fix associativity to avoid parenthesis
-- syntactic sugar
(<$>) :: Proj a args => (HList args -> a) -> Format i args -> SFormat i a
(<$>) = CFormat
(<|>) = Alt

many :: (Stream i Identity Char, StringLike i) => Format i xs -> Format i (Map [] xs)
many p = 
  case toSList p of
    SCons SNil -> cons <$> (p <@> many p)
                  <|> (nil  <$> unit)
    _ -> Many p

-- TODO add support for arbitrary formats
some :: (Stream i Identity Char, StringLike i) => Format i '[ a ]-> Format i '[ [a] ]
some p = cons <$> (p <@> many p )

sepBy :: (Stream i Identity Char, StringLike i, Fill ys) => 
            Format i '[ a ] -> Format i ys -> Format i '[ [ a ] ]
sepBy p sep = (cons <$> (p <@> many (sep @> p)))
           <|>  (nil  <$> unit)

-- Tries each format until one succeeds.
-- The given list must be non empty
choice :: [SFormat i a] -> SFormat i a
choice (x:xs) = foldr (<|>) x xs
choice [] = error "Format.Combinator.choice: empty list"

count :: (Stream i Identity Char, StringLike i) => Int -> SFormat i a -> SFormat i [a]
count n f | n <= 0    = nil <$> unit
count n f | otherwise = cons <$> (f <@> count (n - 1) f)

optional :: (Stream i Identity Char, StringLike i) => SFormat i a -> SFormat i (Maybe a)
optional f = (just <$> f) <|> (nothing <$> unit)

-- Requires IncoherentInstances :(
--(<+>) :: SFormat i a -> SFormat i b -> SFormat i (Either a b)
--f1 <+> f2 = (left <$> f1) <|> (right <$> f2)

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
