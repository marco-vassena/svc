{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Control.Isomorphism.Partial.Prim 
  ( module Control.Isomorphism.Partial.Base
  , inverse
  , (***)
  , (<.>)
  , identity
  , iterate
  , associate
  , foldl
  , element
  , subset
  , unpack
  , zipper
  , combine
  , allEmpty
  , takeWhile
  , takeWhile1
  ) where

import Prelude (($), fst, snd, otherwise, Eq, (==), Bool)
import qualified Prelude as P

import Data.HList
import Data.Maybe
import Data.Proxy

import Control.Category
import Control.Monad
import Control.Isomorphism.Partial.Base
import Control.Isomorphism.Partial.Constructors
import Data.Type.Equality ( (:~:)(Refl) )

inverse :: Iso xs ys -> Iso ys xs
inverse (Iso f g s1 s2) = Iso g f s2 s1

instance Reify2 Iso where
  toSList2 i = (sapply i, sunapply i)

-- | Identity isomorphism. Corresponds to id from Category, however
-- we need a 'SList' object to determine its shape.
identity :: SList xs -> Iso xs xs
identity s = Iso Just Just s s

-- | Compose two isomoprhism. Corresponds to (.) from Category.
(<.>) :: Iso ys zs -> Iso xs ys -> Iso xs zs
(<.>) g f = Iso (apply f >=> apply g) (unapply g >=> unapply f) (sapply f) (sunapply g)

infixr 9 <.>

-- | Repeatedly apply/unapply the given isomorphism until it fails.
iterate :: Iso xs xs -> Iso xs xs
iterate step = Iso f g (sapply step) (sunapply step)
  where f = Just . driver (apply step)
        g = Just . driver (unapply step)

        driver :: (HList xs -> Maybe (HList xs)) -> (HList xs -> HList xs)
        driver step state = maybe state (driver step) (step state)

-- | Joins two isomorphisms, appending inputs and outputs in order.
(***) :: Iso xs ys -> Iso zs ws -> Iso (Append xs zs) (Append ys ws)
i *** j = Iso f g (sappend s1 s3) (sappend s2 s4)
   where (s1, s3) = (sapply i, sapply j)
         (s2, s4) = (sunapply i, sunapply j)
         --f :: HList (Append xs zs) -> Maybe (HList (Append ys ws))
         f hs = liftM2 happend (apply i xs) (apply j zs)
            where (xs, zs) = split s1 s3 hs
         -- g :: HList (Append ys ws) -> Maybe (HList (Append xs zs))
         g hs = liftM2 happend (unapply i ys) (unapply j ws)
            where (ys, ws) = split s2 s4 hs

-- Given an isomorphism that produces a zipper 'HList' returns an isomorphisms
-- that append the two 'HList' one after the other.
unpack :: SameLength as bs -> Iso cs (ZipWith (,) as bs) -> Iso cs (Append as bs)
unpack p i = Iso f g (sapply i) (sappend sAs sBs)
  where (sAs, sBs) = toSList2 p
        f cs = apply i cs >>= return . (P.uncurry happend) . hunzip p
        g cs = unapply i (hzip p as bs)
          where (as, bs) = split sAs sBs cs

-- Uncurry for isomorphisms
uncurry :: Iso '[a, b] '[ c ] -> Iso '[(a , b)] '[ c ]
uncurry i = Iso f g (SCons SNil) (SCons SNil)
  where f (Cons (a, b) _) = apply i $ Cons a (Cons b Nil)
        g hs = unapply i hs >>= return . hsingleton . happly (,)

-- Generalized fold-left for isomoprhisms.
foldl :: SList xs -> Iso (a ': xs) '[ a ] -> Iso (a ': Map [] xs) '[ a ]
foldl s i =  identity (SCons SNil)
         <.> ((identity (SCons SNil)) *** (allEmpty s))
         <.> iterate (step s i)

  where step :: SList xs -> Iso (a ': xs) '[ a ] -> Iso (a ': Map [] xs) (a ': Map [] xs)
        step s i = (i *** identity (smap proxyList s))
                <.> ((identity (SCons SNil)) *** combine s)

-- Transforms a list of empty lists in an empty hlist.
-- If some list is non empty the isomorphism fails.
allEmpty :: SList as -> Iso (Map [] as) '[]
allEmpty SNil = identity SNil
allEmpty (SCons s) = (inverse nil) *** (allEmpty s)

-- | Unpacks each list in head and tail.
-- An hlist containing first all the heads and then all the tails is returned (apply).
-- If some of the input list is empty the isomorphism fails.
combine :: SList xs -> Iso (Map [] xs) (Append xs (Map [] xs))
combine s = unpack (mapPreservesLength proxyList s) (zipper s)

-- | An isomorphism that convert an 'HList' of lists in a zipped 'HList' containing 
-- the head of each list and the tail and vice-versa.
zipper :: SList as -> Iso (Map [] as) (ZipWith (,) as (Map [] as))
zipper SNil = identity SNil
zipper (SCons s) = inverse (uncurry cons) *** zipper s

element :: Eq a => a -> Iso '[ a ] '[]
element x = Iso f g (SCons SNil) SNil
  where f (Cons y _) | x == y       = Just Nil
        f _          | otherwise    = Nothing
        g _ = Just (hsingleton x)

subset :: SList xs -> (HList xs -> Bool) -> Iso xs xs
subset s p = Iso f f s s
  where f hs | p hs      = Just hs
        f hs | otherwise = Nothing

takeWhile :: SList xs -> (HList xs -> Bool) -> Iso (Map [] xs) (Map [] xs) 
takeWhile s p = Iso f f (smap proxyList s) (smap proxyList s)
  where f hs = Just . unList s $ P.takeWhile p (toList s hs)

takeWhile1 :: SList xs -> (HList xs -> Bool) -> Iso (Map [] xs) (Map [] xs) 
takeWhile1 s p = Iso f f (smap proxyList s) (smap proxyList s)
  where f hs = case P.takeWhile p (toList s hs) of
                [] -> Nothing
                xs -> Just (unList s xs)
                

--------------------------------------------------------------------------------
-- TODO maybe remove.

-- | Isomorphisms are associative.
associate :: SList xs -> SList ys -> SList zs -> Iso (Append xs (Append ys zs)) (Append (Append xs ys) zs)
associate s1 s2 s3 = Iso f g (sappend s1 (sappend s2 s3)) (sappend (sappend s1 s2) s3)
  where f hs = case appendAssociative s1 s2 s3 of
                  Refl -> Just hs
        g hs = case appendAssociative s1 s2 s3 of
                  Refl -> Just hs

-- | Isomorphisms are commutative.
commute :: SList xs -> SList ys -> Iso (Append xs ys) (Append ys xs)
commute s1 s2 = Iso (f s1 s2) (f s2 s1) (sappend s1 s2) (sappend s2 s1)
  where f :: SList xs -> SList ys -> HList (Append xs ys) -> Maybe (HList (Append ys xs))
        f s1 s2 hs = Just (happend ys xs)
          where (xs, ys) = split s1 s2 hs
