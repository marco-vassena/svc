{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Control.Isomorphism.Partial.Prim 
  ( module Control.Isomorphism.Partial.Base
  , (***)
  , identity
  , associate
  , unpack
  , zipper
  , combine
  , allEmpty
  , ignore
  , foldl
  , foldr
  , commute
  , (<.>)
  , iff
  ) where

import Prelude (($), fst, snd, otherwise, Eq, (==), Bool)
import qualified Prelude as P

import Data.TypeList.HList
import Data.Maybe
import Data.Proxy

import Control.Category
import Control.Monad
import Control.Applicative
import Control.Isomorphism.Partial.Base
import Control.Isomorphism.Partial.Constructors
import Data.Type.Equality ( (:~:)(Refl) )

instance Reify2 Iso where
  toSList2 i = (sapply i, sunapply i)

-- | Identity isomorphism. Corresponds to id from Category, however
-- we need a 'SList' object to determine its shape.
identity ::  SList xs -> Iso xs xs
identity s = Iso id Just s s

-- Turns a constant isomoprhism in identity
iff :: Iso '[] xs -> Iso xs xs
iff i = Iso f g (sunapply i) (sunapply i)
  where f _  = apply i Nil
        g hs = unapply i hs >> return hs

-- | Compose two isomoprhism. Corresponds to (.) from Category.
(<.>) :: Iso ys zs -> Iso xs ys -> Iso xs zs
(<.>) g f = Iso (apply g . apply f) (unapply g >=> unapply f) (sapply f) (sunapply g)

infixr 9 <.>


infixr 3 ***
-- | Joins two isomorphisms, appending inputs and outputs in order.
(***) ::  Iso xs ys -> Iso zs ws -> Iso (xs :++: zs) (ys :++: ws)
i *** j = Iso f g (sappend s1 s3) (sappend s2 s4)
   where (s1, s3) = (sapply i, sapply j)
         (s2, s4) = (sunapply i, sunapply j)
         f hs = happend (apply i xs) (apply j zs)
            where (xs, zs) = split s1 s3 hs
         g hs = happend <$> (unapply i ys) <*> (unapply j ws)
            where (ys, ws) = split s2 s4 hs

-- Given an isomorphism that produces a zipper 'HList' returns an isomorphisms
-- that append the two 'HList' one after the other.
unpack :: SameLength as bs -> Iso (ZipWith (,) as bs) cs -> Iso (as :++: bs) cs 
unpack p i = Iso f g (sappend sAs sBs) (sunapply i) 
  where (sAs, sBs) = toSList2 p
        f hs = apply i (hzip p as bs)
          where (as, bs) = split sAs sBs hs
        g hs = P.uncurry happend . hunzip p <$> unapply i hs

-- Uncurry for isomorphisms
uncurry :: Iso '[a, b] '[ c ] -> Iso '[(a , b)] '[ c ]
uncurry i = Iso f g (SCons SNil) (SCons SNil)
  where f (Cons (a, b) _) = apply i $ Cons a (Cons b Nil)
        g hs = hsingleton . happly (,) <$> unapply i hs 

invert :: SList ys -> SList zs -> Iso xs (ys :++: zs) -> Iso xs (zs :++: ys)
invert s1 s2 i = Iso f g (sapply i) (sappend s2 s1)
  where switch (hs1, hs2) = happend hs2 hs1
        f hs = switch . split s1 s2 $ apply i hs
        g hs = unapply i . switch $ split s2 s1 hs

swap :: SList xs -> SList ys -> Iso (xs :++: ys) (ys :++: xs)
swap s1 s2 = Iso (f s1 s2) (Just . f s2 s1) (sappend s1 s2) (sappend s2 s1)
  where f s1 s2 = P.uncurry (P.flip happend) . split s1 s2

-- Transforms a list of empty lists in an empty hlist.
-- If some list is non empty the isomorphism fails.
allEmpty ::  SList as -> Iso '[] (Map [] as)
allEmpty SNil = identity SNil
allEmpty (SCons s) = nil *** (allEmpty s)

-- | Unpacks each list in head and tail.
-- An hlist containing first all the heads and then all the tails is returned (apply).
-- If some of the input list is Nothing the isomorphism fails.
combine ::  SList xs -> Iso (xs :++: (Map [] xs)) (Map [] xs) 
combine s = unpack (mapPreservesLength proxyList s) (zipper s)

-- | An isomorphism that convert an 'HList' of lists in a zipped 'HList' containing 
-- the head of each list and the tail and vice-versa.
zipper ::  SList as -> Iso (ZipWith (,) as (Map [] as)) (Map [] as) 
zipper SNil = identity SNil
zipper (SCons s) = uncurry cons *** zipper s

ignore :: HList xs -> Iso xs '[]
ignore hs = Iso f g (toSList hs) SNil
  where f _ = Nil
        g _ = Just hs

-- Generalized foldl.
-- This signature corresponds to the usual:
-- foldl :: (b -> a -> b) -> b -> [ a ] -> b
foldl :: SList as -> Iso (bs :++: as) bs -> Iso (bs :++: (Map [] as)) bs
foldl s1 i = Iso f g (sappend s2 s1') s2
  where s1' = smap proxyList s1
        s2 = sunapply i
        f hs = hfoldl s1 h ys xss
          where (ys, xss) = split s2 s1' hs
                h ys xs = apply i (happend ys xs)
        g zs = Just (happend es hs)
          where h ys = unapply i ys >>= return . split s2 s1
                (es, hs) = hunfoldl s1 h zs

-- Generalized foldr.
-- This signature corresponds to the usual:
-- foldr :: (a -> b -> b) -> b -> [ a ] -> b
foldr :: SList as -> Iso (as :++: bs) bs -> Iso (bs :++: (Map [] as)) bs
foldr s1 i = Iso f g (sappend s2 s1') s2
  where s1' = smap proxyList s1
        s2  = sunapply i
        f hs = hfoldr s1 h ys xss
          where (ys, xss) = split s2 s1' hs
                h xs ys = apply i (happend xs ys)
        g ys = Just $ happend es hs
          where h ys = unapply i ys >>= return . split s1 s2
                (es, hs) = hunfoldr s1 h ys

--------------------------------------------------------------------------------
-- TODO maybe remove.

-- | Isomorphisms are associative.
associate :: SList xs 
          -> SList ys 
          -> SList zs -> Iso (xs :++: (ys :++: zs)) ((xs :++: ys) :++: zs)
associate s1 s2 s3 = Iso f g (sappend s1 (sappend s2 s3)) (sappend (sappend s1 s2) s3)
  where f hs = case appendAssociative s1 s2 s3 of
                  Refl -> hs
        g hs = case appendAssociative s1 s2 s3 of
                  Refl -> Just hs

-- | Isomorphisms are commutative.
commute :: SList xs -> SList ys -> Iso (xs :++: ys) (ys :++: xs)
commute s1 s2 =  Iso (f s1 s2) (Just . f s2 s1) (sappend s1 s2) (sappend s2 s1)
  where f s1 s2 = P.uncurry (P.flip happend) . split s1 s2
