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

data Format (xs :: [ * ]) where
  Seq :: Format xs -> Format ys -> Format (Append xs ys)
  SkipR :: Format xs -> Format ys -> Format xs
  SkipL :: Format xs -> Format ys -> Format ys
  Many :: Format xs -> Format (Map [] xs)
  Target :: Parsable a => Format '[ a ]  
  Meta :: Match a => a -> Format '[]

type Parser i a = Parsec i () a

class ParseMany xs where
  parseMany :: Format xs -> Parser i (HList (Map [] xs))

instance ParseMany '[] where
  parseMany (Meta x) = many (match x) *> return Nil

instance ParseMany '[ a ] where
  parseMany Target = hsingleton <$> many parse
  -- parseMany (Many x) = hsingleton <$> parseMany x
  parseMany (Seq a b)  = append <$> parseMany a <*> parseMany b

class Parsable a where
  parse :: Parser i a

class Match a where
  match :: a -> Parser i a

csv :: (Parsable Int, Match Char) => Format '[ [Int], [Int] ]
csv = Many (Seq (SkipR Target (Meta 'c')) (Target) )

fooFormat :: Parsable Int => Format '[ [[Int]] ]
fooFormat = Many (Many Target)

idS :: Parser i a -> Parser i (Identity a)
idS p = Identity <$> p

mkParser :: Format xs -> Parser i (HList (Map Identity xs))
mkParser f = undefined -- formatMap idS f
--mkParser (Seq a b) = append <$> mkParser a <*> mkParser b
--mkParser (SkipR a b) = mkParser a <* mkParser b
--mkParser (SkipL a b) = mkParser a *> mkParser b
--mkParser Target = hsingleton <$> parse
--mkParser (Meta a) = match a *> pure Nil

-- lifts the many combinators all over the place
formatMap :: (forall a . (Parser i a) -> Parser i (f a)) -> Format xs -> Parser i (HList (Map f xs))
formatMap f Target = hsingleton <$> f parse
formatMap f (Meta a) = f (match a) *> pure Nil
formatMap f (SkipR a b) = formatMap f a <* formatMap f b
formatMap f (SkipL a b) = formatMap f a *> formatMap f b
formatMap f (Many x) = undefined -- do
--  xs <- formatMap f x
--  ys <- formatMap many x
--  case mapComp xs ys f Refl of
--    _ -> return undefined
formatMap f (Seq a b) = undefined

--  xs <- mkParser a
--  ys <- mkParser b 
--  let zs = append xs ys 
--  case mapDist xs ys zs f Refl of
--    Refl -> append <$> formatMap f a <*> formatMap f b

mapDist :: HList xs -> HList ys -> HList zs -> (forall a . Parser i a -> Parser i (f a))
       -> zs :~: Append xs ys -> Append (Map f xs) (Map f ys) :~: Map f zs
mapDist Nil _ _ f Refl = Refl
mapDist (Cons x xs) ys (Cons z zs) f Refl = apply Refl (mapDist xs ys zs f Refl)

mapComp :: HList xs -> HList ys -> (forall a . Parser i a -> Parser i (f [ a ])) 
        -> ys :~: Map [] xs -> Map f ys :~: Map f (Map [] xs)
mapComp Nil _ _ Refl = Refl
mapComp (Cons x xs) (Cons y ys) f Refl = apply Refl (mapComp xs ys f Refl)

mapIden :: HList xs -> HList (Map Identity xs) -> Map Identity xs :~: xs
mapIden Nil _ = Refl
mapIden (Cons x xs) (Cons y ys) = undefined -- apply Refl (mapIden xs ys)
