{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Control.Isomorphism.Partial.Prim where

import Prelude ()

import Data.HList
import Data.Maybe

import Control.Category
import Control.Monad
import Control.Isomorphism.Partial.Constructors

import Data.Type.Equality hiding (apply, unapply)

inverse :: Iso xs ys -> Iso ys xs
inverse (Iso f g s1 s2) = Iso g f s2 s1

apply :: Iso xs ys -> HList xs -> Maybe (HList ys)
apply (Iso f _ _ _) = f

sapply :: Iso xs ys -> SList xs
sapply (Iso _ _ s1 _) = s1

sunapply :: Iso xs ys -> SList ys
sunapply (Iso _ _ _ s2) = s2

unapply :: Iso xs ys -> HList ys -> Maybe (HList xs)
unapply (Iso _ g _ _) = g 

-- | Identity isomorphism. Corresponds to id from Category, however
-- we need 'SList' objects to qualify their shape.
identity :: SList xs -> Iso xs xs
identity s = Iso Just Just s s

-- | Compose two isomoprhism. Corresponds to (.) from Category.
compose :: Iso ys zs -> Iso xs ys -> Iso xs zs
compose g f = Iso (apply f >=> apply g) (unapply g >=> unapply f) (sapply f) (sunapply g)

(<.>) = compose

iterate :: Iso xs xs -> Iso xs xs
iterate step = Iso f g (sapply step) (sunapply step)
  where f = Just . driver (apply step)
        g = Just . driver (unapply step)

        driver :: (HList xs -> Maybe (HList xs)) -> (HList xs -> HList xs)
        driver step state = maybe state (driver step) (step state)

commute :: SList xs -> SList ys -> Iso (Append xs ys) (Append ys xs)
commute s1 s2 = Iso (f s1 s2) (f s2 s1) (sappend s1 s2) (sappend s2 s1)
  where f :: SList xs -> SList ys -> HList (Append xs ys) -> Maybe (HList (Append ys xs))
        f s1 s2 hs = Just (happend ys xs)
          where (xs, ys) = split s1 s2 hs

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

unit :: Iso '[] '[]
unit = identity SNil

associate :: SList xs -> SList ys -> SList zs -> Iso (Append xs (Append ys zs)) (Append (Append xs ys) zs)
associate s1 s2 s3 = Iso f g (sappend s1 (sappend s2 s3)) (sappend (sappend s1 s2) s3)
  where f hs = case propAssociative s1 s2 s3 of
                  Refl -> Just hs
        g hs = case propAssociative s1 s2 s3 of
                  Refl -> Just hs

propAssociative :: SList xs -> SList ys -> SList zs 
                -> HList (Append xs (Append ys zs)) :~: HList (Append (Append xs ys) zs)
propAssociative SNil s2 s3 = Refl
propAssociative (SCons s1) s2 s3 =
  case propAssociative s1 s2 s3 of
    Refl -> Refl

--foldl :: Iso '[a, b] '[ a ] -> Iso '[a, [b]] '[ a ]
--foldl i = inverse unit
--       <.> (identity *** 
