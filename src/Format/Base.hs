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
import Text.Parsec hiding (parse, many, (<|>))
import Control.Applicative
import Data.Type.Equality 
import Data.Functor.Identity
import Data.Monoid
import Data.Maybe

-- Issue with many combinator : 
-- the operator * does not actually distribute over concatenation
-- (ab)* =/= (a*)(b* )
-- Therefore it is not correct to implement a parser for Many 
-- lifting recursively the combinator many in each Format i leaf.
-- We must apply it at top level and unpack [HList xs] to HList [xs]

-- Format representation for data-types
-- Supports total alternatives

-- TODO define synonym for Format with a singleton list

data DFormat i a where
  CFormat :: Proj a args => (HList args -> a) -> Format i args -> DFormat i a
  Alt :: DFormat i a -> DFormat i a -> DFormat i a

data Format i (xs :: [ * ]) where
  Seq :: Format i xs -> Format i ys -> Format i (Append xs ys)
  SkipR :: Fill ys => Format i xs -> Format i ys -> Format i xs
  SkipL :: Fill xs => Format i xs -> Format i ys -> Format i ys
  Many :: Format i xs -> Format i (Map [] xs)

  -- Used for primitive types
  Target :: (Parsable i a, Printable i a) => Format i '[ a ]
  Meta :: (Match i a, Printable i a) => a -> Format i '[]

  -- Used for algebraic data types
  DF :: DFormat i a -> Format i '[ a ]

type Parser i a = Parsec i () a

toSList :: Format i xs -> SList xs
toSList (Seq f1 f2) = sappend (toSList f1) (toSList f2)
toSList (SkipR f1 f2) = toSList f1
toSList (SkipL f1 f2) = toSList f2
toSList (Many f) = smap (undefined :: a -> [] a) (toSList f)
toSList Target = SCons SNil
toSList (Meta _) = SNil
toSList (DF _) = SCons SNil

mkParser :: Format i xs -> Parser i (HList xs)
mkParser (Seq a b) = append <$> mkParser a <*> mkParser b
mkParser (SkipR a b) = mkParser a <* mkParser b
mkParser (SkipL a b) = mkParser a *> mkParser b
mkParser (Many f) = unlist <$> pure (toSList f) <*> many (mkParser f)
mkParser Target = hsingleton <$> parse
mkParser (Meta a) = match a *> pure Nil
mkParser (DF f) = hsingleton <$> mkDParser f

-- Produces a parser for a DFormat
mkDParser :: DFormat i a -> Parser i a
mkDParser (CFormat c fargs) = c <$> mkParser fargs
mkDParser (Alt d1 d2) = mkDParser d1 <|> mkDParser d2

type Printer i a = a -> Maybe i

mkPrinter :: Monoid i => Format i xs -> Printer i (HList xs)
mkPrinter (Seq f1 f2) hs = mappend <$> mkPrinter f1 hs1 <*> mkPrinter f2 hs2
  where (hs1, hs2) = split (toSList f1) (toSList f2) hs
mkPrinter (SkipR x y) xs = mappend <$> mkPrinter x xs <*> mkPrinter y fill
mkPrinter (SkipL x y) ys = mappend <$> mkPrinter x fill <*> mkPrinter y ys
mkPrinter (Many f) hs = mconcat $ map (mkPrinter f) xs
  where xs = toList (toSList f) hs
mkPrinter Target (Cons x Nil) = printer x
mkPrinter (Meta x) Nil = printer x
mkPrinter (DF d) (Cons x Nil) = mkDPrinter d x

mkDPrinter :: Monoid i => DFormat i a -> Printer i a
mkDPrinter (CFormat _ f) a = proj a >>= mkPrinter f 
mkDPrinter (Alt f1 f2) a = 
  case mkDPrinter f1 a of
    Nothing -> mkDPrinter f2 a
    Just s -> Just s

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
--------------------------------------------------------------------------------
class Match i a where
  match :: a -> Parser i a

instance (Stream i Identity Char, StringLike i) => Match i Char where
  match = char

instance (Stream i Identity Char, StringLike i) => Match i () where
  match = pure
--------------------------------------------------------------------------------
class Fill xs where
  fill :: HList xs

instance Fill '[] where
  fill = Nil
--------------------------------------------------------------------------------
-- String like operations
class Monoid i => StringLike i where
  singleton :: Char -> i
  pack :: String -> i

instance StringLike String where
  singleton c = [ c ]
  pack = id

--------------------------------------------------------------------------------
-- Projects an algebraic data type, packing the arguments
-- of the constructors used in a 'HList'.
class Proj a args where
  proj :: a -> Maybe (HList args)
