{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Control.Isomorphism.Partial.Constructors where

import Control.Isomorphism.Partial.Base
import Control.Applicative

import Data.HList

--------------------------------------------------------------------------------
-- Partial isomorphisms for standard data types
--------------------------------------------------------------------------------

-- TODO Define plain Iso rather than CIso

-- Conventient synonim for isomorphisms that target one type
type CIso f xs a = Iso f xs '[ a ]

-- Helper smart constructors that fills the obvious part of the
-- definition for a 'CIso f'.
iso :: Alternative f => (HList xs -> f a) -> (a -> f (HList xs)) -> SList xs -> CIso f xs a
iso from to s = Iso f (to . hHead) s (SCons SNil)
  where f hs = hsingleton <$> from hs

-- All these definitions can be automatically derived using TH
nil :: Alternative f => CIso f '[] [ a ]
nil = iso (pure . const []) proj SNil
  where proj [] = pure Nil
        proj _  = empty

cons :: Alternative f => CIso f '[a , [a]] [ a ]
cons = iso (pure . happly (:)) proj (SCons (SCons SNil))
  where proj (x:xs) = pure $ Cons x (Cons xs Nil)
        proj _      = empty

just :: Alternative f => CIso f '[ a ] (Maybe a) 
just = iso (pure . happly Just) proj (SCons SNil)
  where proj (Just x) = pure (Cons x Nil)
        proj _        = empty

nothing :: Alternative f => CIso f '[] (Maybe a) 
nothing = iso (const empty) proj SNil
  where proj Nothing = pure Nil
        proj _       = empty

left :: Alternative f => CIso f '[ a ] (Either a b)
left = iso (pure . happly Left) proj (SCons SNil)
  where proj (Left x) = pure (Cons x Nil)
        proj _        = empty

right :: Alternative f => CIso f '[ b ] (Either a b) 
right = iso (pure . happly Right) proj (SCons SNil)
  where proj (Right x) = pure (Cons x Nil)
        proj _         = empty
