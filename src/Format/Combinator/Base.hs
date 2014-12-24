{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Format.Combinator.Base where

import Format.Base
import Data.HList
import Control.Applicative ((*>), pure)
import Control.Isomorphism.Partial
import Data.Type.Equality

--------------------------------------------------------------------------------

-- The unit format. The parser succeeds without consuming any input
-- and does not print nothing at all.
unit :: Format m i '[]
unit = Pure Nil

-- | 'between left right f' is a format in which f must occur between 
-- 'left' and 'right'
between :: Format m i '[] -> Format m i '[] -> Format m i xs -> Format m i xs
between l r p = l @> p <@ r

failWith :: Reify f => f xs -> Format m i xs
failWith = Fail . toSList

-- Tries each format until one succeeds.
-- The given list may not be empty.
choice :: [Format m i xs] -> Format m i xs
choice (x:xs) = foldr (<|>) (failWith x) (x:xs)
choice [] = error "Format.Combinator.choice: empty list"

optional :: SFormat m i a -> SFormat m i (Maybe a)
optional f = (just <$> f) <|> (nothing <$> unit)

(<+>) :: SFormat m i a -> SFormat m i b -> SFormat m i (Either a b)
f1 <+> f2 = (left <$> f1) <|> (right <$> f2)

--------------------------------------------------------------------------------
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

