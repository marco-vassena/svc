{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}


-- | This module defines partial isomorphisms for standard types.
-- It should be possible to automatically derive them also for
-- user-defined data types using Template Haskell.

module Control.Isomorphism.Partial.Constructors where

import Control.Isomorphism.Partial.Base
import Control.Applicative

import Data.TypeList.HList
import Data.Char

--------------------------------------------------------------------------------
-- Partial isomorphisms for standard data types
--------------------------------------------------------------------------------

-- Isomorphisms for constructors
type CIso xs a = Iso xs '[ a ]

-- Helper smart constructors that fills the obvious part of the
-- definition for a 'CIso'.
iso :: (HList xs -> a) -> (a -> Maybe (HList xs)) -> SList xs -> CIso xs a
iso from to s = Iso (hsingleton . from) (to . hHead) s (SCons SNil)

--------------------------------------------------------------------------------
-- Lists
--------------------------------------------------------------------------------

nil :: CIso '[] [ a ]
nil = iso (happly []) proj SNil
  where proj [] = Just Nil
        proj _  = Nothing

cons :: CIso '[a , [a]] [ a ]
cons = iso (happly (:)) proj (SCons (SCons SNil))
  where proj (x:xs) = Just $ Cons x (Cons xs Nil)
        proj _      = Nothing

--------------------------------------------------------------------------------
-- Maybe
--------------------------------------------------------------------------------

just :: CIso '[ a ] (Maybe a) 
just = iso (happly Just) proj (SCons SNil)
  where proj (Just x) = Just (Cons x Nil)
        proj _        = Nothing

nothing :: CIso '[] (Maybe a) 
nothing = iso (happly Nothing) proj SNil
  where proj Nothing = Just Nil
        proj _       = Nothing

--------------------------------------------------------------------------------
-- Either
--------------------------------------------------------------------------------

left :: CIso '[ a ] (Either a b)
left = iso (happly Left) proj (SCons SNil)
  where proj (Left x) = Just (Cons x Nil)
        proj _        = Nothing

right :: CIso '[ b ] (Either a b) 
right = iso (happly Right) proj (SCons SNil)
  where proj (Right x) = Just (Cons x Nil)
        proj _         = Nothing

--------------------------------------------------------------------------------
-- Int
--------------------------------------------------------------------------------
-- Transforms a list of digits into a single positive integer
-- e.g. [1,2,3,4] -> 1234

int :: Iso '[[Char]] '[Int]
int = Iso f g slist slist
  where f :: HList '[ [Char] ] -> HList '[Int]
        f (Cons xs Nil) = hsingleton $ list2Int xs
        g :: HList '[ Int ] -> Maybe (HList '[[Char]])
        g (Cons n Nil)  = Just $ hsingleton (int2List n)

int2List :: Int -> [Char]
int2List = reverse . go
  where go n | n < 0 = error "int2List: Only non-negative numbers accepted"
        go n | n < 10 = [ intToDigit n ]
        go n = intToDigit d : go m
          where (m, d) = divMod n 10 

list2Int :: [Char] -> Int
list2Int = foldl (\x y -> x * 10 + (digitToInt y)) 0 
