{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}

-- | This module defines types for describing formats

module Format.Base where

import Control.Isomorphism.Partial
import Control.Applicative
import Control.Monad

import Data.Functor.Identity
import Data.Monoid
import Data.Maybe
import Data.HList

import Text.Parsec hiding (parse, many, (<|>))

-- | 'SFormat' stands for Single Format and represents a 'Format'
-- containing only one target type.
type SFormat i a = Format i '[ a ]

data Format i (xs :: [ * ]) where
  -- Compose formats
  Seq :: Format i xs -> Format i ys -> Format i (Append xs ys)
  SkipR :: Format i xs -> Format i '[] -> Format i xs
  SkipL :: Format i '[] -> Format i ys -> Format i ys
  
  -- Combinator primitives
  Many :: Format i xs -> Format i (Map [] xs)
  Satisfy :: (HList xs -> Bool) -> Format i xs -> Format i xs

  -- Used for primitive types
  Target :: (Parsable i a, Printable i a) => Format i '[ a ]
  Meta :: (Match i a, Printable i a) => a -> Format i '[]

  -- Used for algebraic data types
  CFormat :: Iso args xs -> Format i args -> Format i xs
  Alt :: Format i xs -> Format i xs -> Format i xs

--------------------------------------------------------------------------------
-- Parsing using a format

type Parser i a = Parsec i () a

mkParser :: Format i xs -> Parser i (HList xs)
mkParser (Seq a b) = happend <$> mkParser a <*> mkParser b
mkParser (SkipR a b) = mkParser a <* mkParser b
mkParser (SkipL a b) = mkParser a *> mkParser b
mkParser (Many f) = unList <$> pure (toSList f) <*> many (mkParser f)
mkParser Target = hsingleton <$> parse
mkParser (Meta a) = match a *> pure Nil
mkParser (CFormat i fargs) = try $ do
  args <- mkParser fargs
  case apply i args of
    Just xs -> return xs
    Nothing -> fail "Construcor failed"
mkParser (Alt d1 d2) = mkParser d1 <|> mkParser d2
mkParser (Satisfy p f) = try $ do
  xs <- mkParser f
  if p xs then return xs else fail "Predicate not satisfied"
--------------------------------------------------------------------------------
-- Printing using a format

type Printer i a = a -> Maybe i

mkPrinter :: Monoid i => Format i xs -> Printer i (HList xs)
mkPrinter (Seq f1 f2) hs = mappend <$> mkPrinter f1 hs1 <*> mkPrinter f2 hs2
  where (hs1, hs2) = split (toSList f1) (toSList f2) hs
mkPrinter (SkipR x y) xs = mappend <$> mkPrinter x xs <*> mkPrinter y Nil
mkPrinter (SkipL x y) ys = mappend <$> mkPrinter x Nil <*> mkPrinter y ys
mkPrinter (Many f) hs = mapM (mkPrinter f) xs >>= return . mconcat
  where xs = toList (toSList f) hs
mkPrinter Target (Cons x Nil) = printer x
mkPrinter (Meta x) Nil = printer x
mkPrinter (CFormat i f) xs = 
  case unapply i xs of
    Nothing -> fail "Deconstructor failed"
    Just ys -> mkPrinter f ys
mkPrinter (Alt f1 f2) a = msum [mkPrinter f1 a, mkPrinter f2 a]
mkPrinter (Satisfy p f) xs | p xs      = mkPrinter f xs
mkPrinter (Satisfy p f) xs | otherwise = fail "Predicate not satisfied"

--------------------------------------------------------------------------------
-- Classes and instances
--------------------------------------------------------------------------------
class Parsable i a where
  parse :: Parser i a

instance Stream i Identity Char => Parsable i Int where
  parse = read <$> many1 digit 

instance Stream i Identity Char => Parsable i Char where
  parse = anyChar
--------------------------------------------------------------------------------
-- TODO Maybe could be avoided here
-- TODO Switch order of parameters
class Printable i a where
  printer :: Printer i a

instance StringLike i => Printable i Int where
  printer = pure . pack . show

instance StringLike i => Printable i Char where
  printer = pure . singleton

instance StringLike i => Printable i () where
  printer () = pure mempty

instance StringLike i => Printable i String where
  printer = pure . pack

--------------------------------------------------------------------------------
class Match i a where
  match :: a -> Parser i a

type StreamChar i = (Stream i Identity Char, StringLike i)

instance StreamChar i => Match i Char where
  match = char

instance StreamChar i => Match i () where
  match = pure

instance StreamChar i => Match i String where
  match = string 

--------------------------------------------------------------------------------
-- String like operations
class Monoid i => StringLike i where
  singleton :: Char -> i
  pack :: String -> i

instance StringLike String where
  singleton c = [ c ]
  pack = id

--------------------------------------------------------------------------------
instance Reify (Format i) where
  toSList (Seq f1 f2) = sappend (toSList f1) (toSList f2)
  toSList (SkipR f1 f2) = toSList f1
  toSList (SkipL f1 f2) = toSList f2
  toSList (Many f) = smap (undefined :: a -> [] a) (toSList f)
  toSList Target = SCons SNil
  toSList (Meta _) = SNil
  toSList (CFormat i _) = sunapply i
  toSList (Alt f1 f2) = toSList f1
  toSList (Satisfy p f) = toSList f
