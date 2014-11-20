{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Format.Decode where

import Control.Applicative ((<$>), (<*>), (*>), (<*))
import Control.Monad.Identity
import Data.Monoid
import Data.Proxy
import Format.Base
import GHC.TypeLits
import Text.Parsec.Prim
import Text.Parsec.Combinator
import Text.Parsec.Char

type Parser i a = Parsec i () a

class Decode i a where
  gdecode :: Parser i a

instance (Monoid i, Decode i a, Decode i b) => Decode i (a :*: b) where
  gdecode = (:*:) <$> gdecode <*> gdecode

instance (Monoid i, Decode i a, Decode i b) => Decode i (a :+: b) where
  gdecode = (L <$> gdecode) <|> (R <$> gdecode)

instance (Monoid i, Decode i a) => Decode i (Many a) where
  gdecode = Many <$> many (gdecode)

instance (Monoid i, Decode i a) => Decode i (Some a) where
  gdecode = Some <$> gdecode <*> many gdecode

instance Stream i Identity Char => Decode i Int where
  gdecode = read <$> many1 digit

instance Stream i Identity Char => Decode i Char where
  gdecode = anyChar

--------------------------------------------------------------------------------

-- An auxiliary class used to recognize type level strings and numbers.
class DecodeKindLit i s  where
  gdecodeKind :: Proxy s -> Parser i (Proxy s)

instance (Stream i Identity Char, KnownSymbol s) => DecodeKindLit i s where
  gdecodeKind p = string (symbolVal p) *> return Proxy

instance (Stream i Identity Char, KnownNat s) => DecodeKindLit i s where
  -- TODO not sure if this is a sensible definition
  gdecodeKind p = string (show (natVal p)) *> return Proxy

--------------------------------------------------------------------------------

-- An auxiliary class that abstracs context sensitive decoding.
-- The user is expected to implement this instance.
class DecodeWith i a b where
  decodeWith :: a -> Parser i b

instance (Decode i a, DecodeWith i a b) => Decode i (a :~>: b) where
  -- Monadic code denotes context sensitive parsing
  gdecode = do
    a <- gdecode
    b <- decodeWith a
    return (a :~>: b)
