{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}

-- | In order to unify parsing and printing, formats
-- are represented directly as a /universe/,
-- from which inverse-by-construction parser and printer
-- can be derived as /interpretation/.
-- The /universe/ is _open_, so that new primitives can be
-- defined at any time.
-- The descriptors have the form @a c m i xs@, the parameters
-- must have the same kinds:
-- 
-- * @c@ is a constraint type constructor (see examples).
-- * @m :: * -> *@ is the semantics parameter.
-- * @i :: *@ is the token type.
-- * @xs :: [ * ]@ are the types involved in a format.
--
-- This module defines the @Format@ wrapper descriptor,
-- which is used only to unify the signatures, which
-- otherwise would be to overly complicated.
-- In particular all the concrete descriptor defined
-- in the other modules provide smart constructors, that 
-- wrap their single data types in @Format@.


module Format.Syntax.Base (
    Reify(..)
  , Format(..)
  , format
  , Use(..)
  , SFormat ) where

import Prelude ((.), Bool(..), const, String)
import Data.TypeList.HList
import Data.Type.Equality
import GHC.Exts

-- A wrapper format descriptor. 
-- Its semantics correspond to the semantics of the wrapped format.
-- Note that this wrapper is used just for convenience, but it does
-- not "close" the format universe.
data Format c (m :: * -> *) (i :: *) (xs :: [*]) where
  Format :: (Reify (a m i), c m i a) => a m i xs -> Format c m i xs

-- A more readable constraint type-synonym.
-- In a signature, the constraint @Use a c m i@ means that the format descriptor @a@ 
-- is used in the implementation.
type Use a c m i = c m i (a c)

-- Smart constructor for @Format@.
format :: (Use a c m i, Reify (a c m i)) => a c m i xs -> Format c m i xs
format = Format

-- | 'SFormat' stands for Single Format and represents a 'Format'
-- containing only one target type.
type SFormat c m i a = Format c m i '[ a ]

instance Reify (Format c m i) where
  toSList (Format f) = toSList f
