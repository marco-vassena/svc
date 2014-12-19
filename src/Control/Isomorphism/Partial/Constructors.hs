{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}

module Control.Isomorphism.Partial.Constructors where

import Control.Isomorphism.Partial.Base
import Control.Monad

import Data.HList

--------------------------------------------------------------------------------
-- Partial isomorphisms for standard data types
--------------------------------------------------------------------------------

-- Conventient synonim for isomorphisms that target one type
type CIso xs a = Iso xs '[ a ]

-- Helper smart constructors that fills the obvious part of the
-- definition for a 'CIso'.
iso :: (HList xs -> a) -> (a -> Maybe (HList xs)) -> SList xs -> CIso xs a
iso from to s = Iso (Just . hsingleton . from) (to . hHead) s (SCons SNil)

-- All these definitions can be automatically derived using TH
nil :: CIso '[] [ a ]
nil = iso (const []) proj SNil
  where proj [] = Just Nil
        proj _  = Nothing

cons :: CIso '[a , [a]] [ a ]
cons = iso (happly (:)) proj (SCons (SCons SNil))
  where proj (x:xs) = Just $ Cons x (Cons xs Nil)
        proj _      = Nothing

just :: CIso '[ a ] (Maybe a) 
just = iso (happly Just) proj (SCons SNil)
  where proj (Just x) = Just (Cons x Nil)
        proj _        = Nothing

nothing :: CIso '[] (Maybe a) 
nothing = iso (const Nothing) proj SNil
  where proj Nothing = Just Nil
        proj _       = Nothing

left :: CIso '[ a ] (Either a b)
left = iso (happly Left) proj (SCons SNil)
  where proj (Left x) = Just (Cons x Nil)
        proj _        = Nothing

right :: CIso '[ b ] (Either a b) 
right = iso (happly Right) proj (SCons SNil)
  where proj (Right x) = Just (Cons x Nil)
        proj _         = Nothing
