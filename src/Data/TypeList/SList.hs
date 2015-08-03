{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module Data.TypeList.SList (
    module Data.TypeList.Core
  , SList(..)
  , sappend
  , smap
  , Reify(..)
  , Reify2(..)
  , KnownSList(..)
  ) where

import Data.Proxy
import Data.TypeList.Core


-- The singleton type of lists, which allows us to take a list as a
-- term-level and a type-level argument at the same time.
-- It is used to retrieve information about the shape of an
-- 'HList' at runtime.
data SList xs where
 SNil :: SList '[]
 SCons :: SList xs -> SList (x ': xs)

-- | Append function for the singleton type 'SList'.
sappend :: SList xs -> SList ys -> SList (xs :++: ys)
sappend SNil ys = ys
sappend (SCons xs) ys = SCons (sappend xs ys)

-- | Map function for the singleton type SList.
smap :: Proxy f -> SList xs -> SList (Map f xs)
smap _ SNil = SNil
smap p (SCons xs) = SCons (smap p xs) 

-- | A class of objects parametrized over a type level list 
class Reify f where
  -- | Return the 'SList' witness object for the parametrized list.
  toSList :: f xs -> SList xs

-- A class of objects parametrized over two type level lists
class Reify2 f where
  -- | Returns the 'SList' witness object for both the parametrized lists.
  toSList2 :: f xs ys -> (SList xs, SList ys)

--------------------------------------------------------------------------------

class KnownSList xs where
  slist :: SList xs

instance KnownSList '[] where
  slist = SNil

instance KnownSList xs => KnownSList (x ': xs) where
  slist = SCons slist

