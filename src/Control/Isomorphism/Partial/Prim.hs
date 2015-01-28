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
  , ignore
  ) where

import Prelude (($), fst, snd, otherwise, Eq, (==), Bool)
import qualified Prelude as P

import Data.HList
import Data.Maybe
import Data.Proxy

import Control.Category
import Control.Monad
import Control.Applicative
import Control.Isomorphism.Partial.Base
import Control.Isomorphism.Partial.Constructors
import Data.Type.Equality ( (:~:)(Refl) )

inverse :: Iso f xs ys -> Iso f ys xs
inverse (Iso f g s1 s2) = Iso g f s2 s1

instance Reify2 (Iso f) where
  toSList2 i = (sapply i, sunapply i)

-- | Identity isomorphism. Corresponds to id from Category, however
-- we need a 'SList' object to determine its shape.
identity :: Applicative f => SList xs -> Iso f xs xs
identity s = Iso pure pure s s

-- | Compose two isomoprhism. Corresponds to (.) from Category.
(<.>) :: Monad f => Iso f ys zs -> Iso f xs ys -> Iso f xs zs
(<.>) g f = Iso (apply f >=> apply g) (unapply g >=> unapply f) (sapply f) (sunapply g)

infixr 9 <.>

-- | Repeatedly apply/unapply the given isomorphism until it fails.
iterate :: Iso Maybe xs xs -> Iso Maybe xs xs
iterate step = Iso f g (sapply step) (sunapply step)
  where f = pure . driver (apply step)
        g = pure . driver (unapply step)

        driver :: (HList xs -> Maybe (HList xs)) -> (HList xs -> HList xs)
        driver step state = maybe state (driver step) (step state)

infixr 3 ***
-- | Joins two isomorphisms, appending inputs and outputs in order.
(***) :: Applicative f => Iso f xs ys -> Iso f zs ws -> Iso f (Append xs zs) (Append ys ws)
i *** j = Iso f g (sappend s1 s3) (sappend s2 s4)
   where (s1, s3) = (sapply i, sapply j)
         (s2, s4) = (sunapply i, sunapply j)
         f hs = happend <$> (apply i xs) <*> (apply j zs)
            where (xs, zs) = split s1 s3 hs
         g hs = happend <$> (unapply i ys) <*> (unapply j ws)
            where (ys, ws) = split s2 s4 hs

-- Given an isomorphism that produces a zipper 'HList' returns an isomorphisms
-- that append the two 'HList' one after the other.
unpack :: Functor f => SameLength as bs -> Iso f cs (ZipWith (,) as bs) -> Iso f cs (Append as bs)
unpack p i = Iso f g (sapply i) (sappend sAs sBs)
  where (sAs, sBs) = toSList2 p
        f cs = (P.uncurry happend) . hunzip p <$> apply i cs 
        g cs = unapply i (hzip p as bs)
          where (as, bs) = split sAs sBs cs

-- Uncurry for isomorphisms
uncurry :: Functor f => Iso f '[a, b] '[ c ] -> Iso f '[(a , b)] '[ c ]
uncurry i = Iso f g (SCons SNil) (SCons SNil)
  where f (Cons (a, b) _) = apply i $ Cons a (Cons b Nil)
        g hs = hsingleton . happly (,) <$> unapply i hs 

-- Generalized fold-left for isomoprhisms.
foldl :: SList xs -> Iso Maybe (a ': xs) '[ a ] -> Iso Maybe (a ': Map [] xs) '[ a ]
foldl s i =  identity (SCons SNil)
         <.> ((identity (SCons SNil)) *** (allEmpty s))
         <.> iterate (step s i)

  where step :: (Alternative f, Monad f) => SList xs -> Iso f (a ': xs) '[ a ] -> Iso f (a ': Map [] xs) (a ': Map [] xs)
        step s i = (i *** identity (smap proxyList s))
                <.> ((identity (SCons SNil)) *** combine s)

invert :: Alternative f 
       => SList ys -> SList zs -> Iso f xs (Append ys zs) -> Iso f xs (Append zs ys)
invert s1 s2 i = Iso f g (sapply i) (sappend s2 s1)
  where switch (hs1, hs2) = happend hs2 hs1
        f hs = switch . split s1 s2 <$> apply i hs
        g hs = unapply i . switch $ split s2 s1 hs

-- Transforms a list of empty lists in an empty hlist.
-- If some list is non empty the isomorphism fails.
allEmpty :: Alternative f => SList as -> Iso f (Map [] as) '[]
allEmpty SNil = identity SNil
allEmpty (SCons s) = (inverse nil) *** (allEmpty s)

-- | Unpacks each list in head and tail.
-- An hlist containing first all the heads and then all the tails is returned (apply).
-- If some of the input list is empty the isomorphism fails.
combine :: Alternative f => SList xs -> Iso f (Map [] xs) (Append xs (Map [] xs))
combine s = unpack (mapPreservesLength proxyList s) (zipper s)

-- | An isomorphism that convert an 'HList' of lists in a zipped 'HList' containing 
-- the head of each list and the tail and vice-versa.
zipper :: Alternative f => SList as -> Iso f (Map [] as) (ZipWith (,) as (Map [] as))
zipper SNil = identity SNil
zipper (SCons s) = inverse (uncurry cons) *** zipper s

element :: (Alternative f, Eq a) => a -> Iso f '[ a ] '[]
element x = Iso f g (SCons SNil) SNil
  where f (Cons y _) | x == y       = pure Nil
        f _          | otherwise    = empty
        g _ = pure (hsingleton x)

subset :: Alternative f => SList xs -> (HList xs -> Bool) -> Iso f xs xs
subset s p = Iso f f s s
  where f hs | p hs      = pure hs
        f hs | otherwise = empty

ignore :: Applicative f => HList xs -> Iso f xs '[]
ignore hs = Iso f g (toSList hs) SNil
  where f _ = pure Nil
        g _ = pure hs

--------------------------------------------------------------------------------
-- TODO maybe remove.

-- | Isomorphisms are associative.
associate :: Applicative f 
          => SList xs 
          -> SList ys 
          -> SList zs -> Iso f (Append xs (Append ys zs)) (Append (Append xs ys) zs)
associate s1 s2 s3 = Iso f g (sappend s1 (sappend s2 s3)) (sappend (sappend s1 s2) s3)
  where f hs = case appendAssociative s1 s2 s3 of
                  Refl -> pure hs
        g hs = case appendAssociative s1 s2 s3 of
                  Refl -> pure hs

-- | Isomorphisms are commutative.
commute :: Applicative f => SList xs -> SList ys -> Iso f (Append xs ys) (Append ys xs)
commute s1 s2 = Iso (f s1 s2) (f s2 s1) (sappend s1 s2) (sappend s2 s1)
  where f :: Applicative f => SList xs -> SList ys -> HList (Append xs ys) -> f (HList (Append ys xs))
        f s1 s2 hs = pure (happend ys xs)
          where (xs, ys) = split s1 s2 hs
