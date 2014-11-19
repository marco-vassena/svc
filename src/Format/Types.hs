{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}

module Format.Types where

import Data.Attoparsec.Types
import Data.Attoparsec.Combinator
import Data.Monoid
import Data.Proxy
import Control.Applicative

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

-- Defines the encoding / decoding functions for a DataFormat
class DataFormat i a where
  decode :: Parser i a
  encode :: a -> i

instance (Monoid i, DataFormat i a, DataFormat i b) => DataFormat i (a :*: b) where
  decode = (:*:) <$> decode <*> decode
  encode (a :*: b) = encode a <> encode b

instance (Monoid i, DataFormat i a, DataFormat i b) => DataFormat i (a :+: b) where
  decode = (L <$> decode) <|> (R <$> decode)
  encode (L a) = encode a
  encode (R b) = encode b

instance (Monoid i, DataFormat i a) => DataFormat i (Many a) where
  decode = Many <$> many (decode)
  encode (Many as) = mconcat (fmap encode as)

instance (Monoid i, DataFormat i a) => DataFormat i (Some a) where
  decode = Some <$> decode <*> many decode
  encode (Some a as) = mconcat (fmap encode (a : as))

-- An auxiliary class used to recognize type level strings and numbers.
class DecodeKindLit i s  where
  decodeKind :: Proxy s -> Parser i (Proxy s)

-- An auxiliary class that abstracs context sensitive decoding.
-- The user is expected to implement this instance.
class DecodeWith i a b where
  decodeWith :: a -> Parser i b

instance (Monoid i, DataFormat i a, DataFormat i b, DecodeWith i a b) => DataFormat i (a :~>: b) where
  -- Monadic code denotes context sensitive parsing
  decode = do
    a <- decode
    b <- decodeWith a
    return (a :~>: b)
  encode (a :~>: b) = encode a <> encode b
