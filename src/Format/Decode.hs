{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

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

instance (Stream i Identity t, Decode i a) => Decode i (Maybe a) where
  gdecode = optionMaybe gdecode

instance Stream i Identity Char => Decode i Int where
  gdecode = read <$> many1 digit

instance Stream i Identity Char => Decode i Char where
  gdecode = anyChar

instance WithProxy i Proxy s => Decode i (Proxy s) where
  gdecode = withProxy Proxy

instance (Stream i Identity Char, KnownSymbol s, WithProxy i NoneOf s) => Decode i (NoneOf s) where
  gdecode = withProxy Proxy

--------------------------------------------------------------------------------

-- An auxiliary class needed to deal with type level information.
-- In order to satisfy the type-checker the argument Proxy s is required
class WithProxy i (f :: k -> *) (s :: k) where
  withProxy :: Proxy s -> Parser i (f s)

instance (Stream i Identity Char, KnownSymbol s) => WithProxy i NoneOf s where
  withProxy p = NoneOf Proxy <$> (noneOf cs)
    where cs = symbolVal p

instance (Stream i Identity Char, KnownSymbol s) => WithProxy i Proxy s where
  withProxy p = string (symbolVal p) *> return Proxy

instance (Stream i Identity Char, KnownNat s) => WithProxy i Proxy s where
  -- TODO not sure if this is a sensible definition
  withProxy p = string (show (natVal p)) *> return Proxy

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
