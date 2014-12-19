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
  ) where

import Prelude (($), fst, snd)
import qualified Prelude as P

import Data.HList
import Data.Maybe

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

-- Given an isomorphism that produces a zipped 'HList' returns an isomorphisms
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
         <.> ((identity (SCons SNil)) *** (idInverseNil s))
         <.> iterate (step s i)

  where step :: SList xs -> Iso (a ': xs) '[ a ] -> Iso (a ': Map [] xs) (a ': Map [] xs)
        step s i = (i *** identity (smap (\_ -> []) s))
                <.> ((identity (SCons SNil)) *** idInverseCons s)

        idInverseNil :: SList as -> Iso (Map [] as) '[]
        idInverseNil SNil = identity SNil
        idInverseNil (SCons s) = (inverse nil) *** (idInverseNil s)

        idInverseCons :: SList as -> Iso (Map [] as) (Append as (Map [] as))
        idInverseCons s = unpack (mapPreservesLength s (\_ -> [])) (zipped s)
          where zipped :: SList as -> Iso (Map [] as) (ZipWith (,) as (Map [] as))
                zipped SNil = identity SNil
                zipped (SCons s) = inverse (uncurry cons) *** zipped s
 
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
