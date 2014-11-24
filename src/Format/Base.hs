{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module defines types for describing formats

module Format.Base where

import Data.Proxy
import GHC.TypeLits
import Format.HList

-- Sequence
data a :*: b = a :*: b

-- Alternative
data a :+: b = L a
             | R b

-- Zero or more
data Many a = Many [a]

-- One or more
data Some a = Some a [a]

-- | Context sensitive decoding
-- The parser of b depends on the value a.
-- The user is required to write an instance for DecodeWith i a b
-- that specifies how the value a is used to produce a parser for b.
data a :~>: b = a :~>: b

-- | Match any character except those included in s
data NoneOf (s :: Symbol) = NoneOf (Proxy s) Char

-- Similar to their applicative counterparts, one component 
-- is discarded.
data a :*>: b = a :*>: b
data a :<*: b = a :<*: b

-- Exactly n 
-- type a :^: (n :: Nat) = Vector a n

--data Vector (a :: *) (n :: Nat) where
--  Nil :: Vector a 0
--  Cons :: a -> Vector a n -> Vector a (n + 1)

type family Collect a :: [ * ] where
  Collect (a :*: b) = Append (Collect a) (Collect b)
  Collect (Many a) = Map [] (Collect a)
  Collect (a :*>: b) = Collect b
  Collect (a :<*: b) = Collect a
  Collect (Proxy s) = '[]
  Collect a = '[ a ]

class Children a where
  children :: a -> HList (Collect a)

instance (Children a, Children b) => Children (a :*: b) where
  children (a :*: b) = append (children a) (children b) 

instance Children a => Children (a :<*: b) where
  children (a :<*: b) = children a

instance Children b => Children (a :*>: b) where
  children (a :*>: b) = children b

instance Children a => Children (Many a) where
  children (Many xs) = undefined -- Cons (concatMap children xs) Nil

instance Children (Proxy x) where
  children _ = Nil

instance Children Int where
  children i = Cons i Nil
