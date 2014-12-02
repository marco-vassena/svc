{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-} -- Remove
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}

-- | This module defines types for describing formats


module Format.Base where

import Format.HList
import Text.Parsec hiding (parse, many)
import Control.Applicative
import Data.Type.Equality 
import Data.Functor.Identity

-- Issue with many combinator : 
-- the operator * does not actually distribute over concatenation
-- (ab)* =/= (a*)(b* )
-- Therefore it is not correct to implement a parser for Many 
-- lifting recursively the combinator many in each Format leaf.
-- We must apply it at top level and unpack [HList xs] to HList [xs]

data Format (xs :: [ * ]) where
  Seq :: Format xs -> Format ys -> Format (Append xs ys)
  SkipR :: Format xs -> Format ys -> Format xs
  SkipL :: Format xs -> Format ys -> Format ys
  Many :: Format xs -> Format (Map [] xs)
  Target :: Parsable a => Format '[ a ]  
  Meta :: Match a => a -> Format '[]

type Parser i a = Parsec i () a

class Parsable a where
  parse :: Parser i a

class Match a where
  match :: a -> Parser i a

toSList :: Format xs -> SList xs
toSList (Seq f1 f2) = sappend (toSList f1) (toSList f2)
toSList (SkipR f1 f2) = toSList f1
toSList (SkipL f1 f2) = toSList f2
toSList (Many f) = smap (undefined :: a -> [] a) (toSList f)
toSList Target = SCons SNil
toSList (Meta _) = SNil

mkParser :: Format xs -> Parser i (HList xs)
mkParser (Seq a b) = append <$> mkParser a <*> mkParser b
mkParser (SkipR a b) = mkParser a <* mkParser b
mkParser (SkipL a b) = mkParser a *> mkParser b
mkParser (Many f) = unlist <$> pure (toSList f) <*> many (mkParser f)
mkParser Target = hsingleton <$> parse
mkParser (Meta a) = match a *> pure Nil

--------------------------------------------------------------------------------
