{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Format.ByteString where

import Control.Applicative
import Data.Attoparsec.ByteString
import Data.Attoparsec.ByteString.Char8 (anyChar, decimal, signed)
import Data.Proxy
import Data.ByteString.Char8 
import Format.Types
import GHC.TypeLits

instance DataFormat ByteString Char where
  decode = anyChar
  encode = singleton

instance DataFormat ByteString Int where
  decode = decimal
  encode = pack . show

instance (KnownSymbol s) => DecodeKindLit ByteString s where
  decodeKind p = string symbol *> return Proxy
    where symbol = pack (symbolVal p)

instance (KnownNat n) => DecodeKindLit ByteString n where
  decodeKind p = string nat *> return Proxy
    where nat = pack $ show $ natVal p

instance (DecodeKindLit ByteString s, KnownSymbol s) => DataFormat ByteString (Proxy s) where
  decode = decodeKind Proxy
  encode = pack . symbolVal

instance (DecodeKindLit ByteString s, KnownNat s) => DataFormat ByteString (Proxy s) where
  decode = decodeKind Proxy
  encode = pack . show . natVal

parseFormat :: DataFormat ByteString a => Parser a -> ByteString -> Either String a
parseFormat p = parseOnly (p <* endOfInput)
