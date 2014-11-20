{-# LANGUAGE TypeOperators #-}

-- | This module defines types for describing formats

module Format.Base where

-- Sequence
data a :*: b = a :*: b

-- Alternative
data a :+: b = L a
             | R b

-- Zero or more
data Many a = Many [a]

-- One or more
data Some a = Some a [a]

-- Context sensitive decoding
-- The parser of b depends on the value a.
data a :~>: b = a :~>: b

-- Exactly n 
-- type a :^: (n :: Nat) = Vector a n

--data Vector (a :: *) (n :: Nat) where
--  Nil :: Vector a 0
--  Cons :: a -> Vector a n -> Vector a (n + 1)
