{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module defines types for describing formats

module Format.Base where

import Format.HList
import Text.Parsec hiding (parse, many)
import Control.Applicative
import Data.Type.Equality 
import Data.Functor.Identity
import Data.Monoid

-- Issue with many combinator : 
-- the operator * does not actually distribute over concatenation
-- (ab)* =/= (a*)(b* )
-- Therefore it is not correct to implement a parser for Many 
-- lifting recursively the combinator many in each Format i leaf.
-- We must apply it at top level and unpack [HList xs] to HList [xs]

data Format i (xs :: [ * ]) where
  Seq :: Format i xs -> Format i ys -> Format i (Append xs ys)
  SkipR :: Fill ys => Format i xs -> Format i ys -> Format i xs
  SkipL :: Fill xs => Format i xs -> Format i ys -> Format i ys
  Many :: Format i xs -> Format i (Map [] xs)
  Target :: (Parsable i a, Printable i a) => Format i '[ a ]
  Meta :: (Match i a, Printable i a) => a -> Format i '[]

type Parser i a = Parsec i () a

toSList :: Format i xs -> SList xs
toSList (Seq f1 f2) = sappend (toSList f1) (toSList f2)
toSList (SkipR f1 f2) = toSList f1
toSList (SkipL f1 f2) = toSList f2
toSList (Many f) = smap (undefined :: a -> [] a) (toSList f)
toSList Target = SCons SNil
toSList (Meta _) = SNil

mkParser :: Format i xs -> Parser i (HList xs)
mkParser (Seq a b) = append <$> mkParser a <*> mkParser b
mkParser (SkipR a b) = mkParser a <* mkParser b
mkParser (SkipL a b) = mkParser a *> mkParser b
mkParser (Many f) = unlist <$> pure (toSList f) <*> many (mkParser f)
mkParser Target = hsingleton <$> parse
mkParser (Meta a) = match a *> pure Nil

type Printer i a = a -> i

mkPrinter :: Monoid i => Format i xs -> Printer i (HList xs)
mkPrinter (Seq f1 f2) hs = mkPrinter f1 hs1 <> mkPrinter f2 hs2
  where (hs1, hs2) = split (toSList f1) (toSList f2) hs
mkPrinter (SkipR x y) xs = mkPrinter x xs <> mkPrinter y fill
mkPrinter (SkipL x y) ys = mkPrinter x fill <> mkPrinter y ys
mkPrinter (Many f) hs = mconcat $ map (mkPrinter f) xs
  where xs = toList (toSList f) hs
mkPrinter Target (Cons x Nil) = printer x
mkPrinter (Meta x) Nil = printer x

--------------------------------------------------------------------------------
-- Syntactic sugar - applicative-like style
(<@>) :: Format i xs -> Format i ys -> Format i (Append xs ys)
(<@>) = Seq

(<@) :: Fill ys => Format i xs -> Format i ys -> Format i xs
(<@) = SkipR 

(@>) :: Fill xs => Format i xs -> Format i ys -> Format i ys
(@>) = SkipL 

--------------------------------------------------------------------------------
-- Classes and instances
--------------------------------------------------------------------------------
class Parsable i a where
  parse :: Parser i a

instance Stream i Identity Char => Parsable i Int where
  parse = read <$> many1 digit 
--------------------------------------------------------------------------------
class Printable i a where
  printer :: Printer i a

instance StringLike i => Printable i Int where
  printer = pack . show

instance StringLike i => Printable i Char where
  printer = singleton
--------------------------------------------------------------------------------
class Match i a where
  match :: a -> Parser i a

instance (Stream i Identity Char, StringLike i) => Match i Char where
  match = char
--------------------------------------------------------------------------------
class Fill xs where
  fill :: HList xs

instance Fill '[] where
  fill = Nil
--------------------------------------------------------------------------------
-- String like operations
class StringLike i where
  singleton :: Char -> i
  pack :: String -> i

instance StringLike String where
  singleton c = [ c ]
  pack = id
