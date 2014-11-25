{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}

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
  Collect (Many a) = Collect [ a ] 
  Collect (a :*>: b) = Collect b
  Collect (a :<*: b) = Collect a
  Collect (Proxy s) = '[]
  Collect [ a ] = Map [] (Collect a)
  Collect a = '[ a ]


class Children a where
  children :: a -> HList (Collect a)

instance (Children a, Children b) => Children (a :*: b) where
  children (a :*: b) = append (children a) (children b) 

instance Children a => Children (a :<*: b) where
  children (a :<*: b) = children a

instance Children b => Children (a :*>: b) where
  children (a :*>: b) = children b

--hmap' :: Children a => (a -> [a]) -> HList (Collect a) -> HList (Map [] (Collect a))
--hmap' f Nil = Nil
--hmap' f (Cons x xs) = Cons (f x) (hmap f xs)

instance Children a => Children (Many a) where
  children (Many xs) = children xs

instance Children a => Children [ a ] where

--  children (x:xs) = case (hmap (:[]) (children x), children xs) of
--                         (ys, Nil) -> ys
--                         (ys, Cons x xs) -> ys
  children xs = undefined 
-- Cons (map children xs) Nil
--case children x of
--                      Nil -> children xs
--                      Cons y ys -> hmap (:[]) (Cons y ys) 
--    where y = children x
--          ys = children xs

instance Children (Proxy x) where
  children _ = Nil

instance Children Int where
  children i = Cons i Nil
