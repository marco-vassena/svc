{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Format.Types where

import Text.Parsec.ByteString ()
import Text.Parsec.Text ()
import Text.Parsec
import Text.Parsec.Prim
import Text.Parsec.Combinator
import Text.Parsec.Char
import Data.Monoid
import Data.Proxy
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as B
import Data.Text (Text)
import qualified Data.Text as T
import Control.Applicative ((<$>), (<*>), (*>), (<*))
import Control.Monad.Identity
import GHC.TypeLits

type Parser i a = Parsec i () a

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

-- Used to parse a format described in a DataFormat instance.
-- It requires the whole input to be consumed.
parseFormat :: (DataFormat i a, Stream i Identity t, Show t) => Parser i a -> i -> Either ParseError a
parseFormat p = parse (p <* eof) ""

parseTest :: (DataFormat i a, Stream i Identity t, Show i, Show t) => Parser i a -> i -> IO ()
parseTest p input = 
  case parseFormat p input of
    Left err -> do 
      putStr "parse error at "
      print err
    Right x -> putStrLn $ show $ (encode x) `asTypeOf` input

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

decodeInt :: Stream i Identity Char => Parser i Int
decodeInt = read <$> many1 digit

--------------------------------------------------------------------------------
-- ByteString instances

instance DataFormat ByteString Char where
  decode = anyChar
  encode = B.singleton

instance DataFormat ByteString Int where
  decode = decodeInt
  encode = B.pack . show

instance (KnownSymbol s, DecodeKindLit ByteString s) => DataFormat ByteString (Proxy s) where
  decode = decodeKind Proxy
  encode = B.pack . symbolVal

instance (KnownNat n, DecodeKindLit ByteString n) => DataFormat ByteString (Proxy n) where
  decode = decodeKind Proxy
  encode = B.pack . show . natVal 

--------------------------------------------------------------------------------
-- Text instances 

instance DataFormat Text Char where
  decode = anyChar
  encode = T.singleton

instance DataFormat Text Int where
  decode = decodeInt
  encode = T.pack . show

instance (KnownSymbol s, DecodeKindLit Text s) => DataFormat Text (Proxy s) where
  decode = decodeKind Proxy
  encode = T.pack . symbolVal

instance (KnownNat n, DecodeKindLit Text n) => DataFormat Text (Proxy n) where
  decode = decodeKind Proxy
  encode = T.pack . show . natVal 

--------------------------------------------------------------------------------
-- An auxiliary class used to recognize type level strings and numbers.
class DecodeKindLit i s  where
  decodeKind :: Proxy s -> Parser i (Proxy s)

instance (Stream i Identity Char, KnownSymbol s) => DecodeKindLit i s where
  decodeKind p = string (symbolVal p) *> return Proxy

instance (Stream i Identity Char, KnownNat s) => DecodeKindLit i s where
  -- TODO not sure if this is a sensible definition
  decodeKind p = string (show (natVal p)) *> return Proxy

--------------------------------------------------------------------------------

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
