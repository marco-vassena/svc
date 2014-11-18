{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Format.Text where

import Control.Applicative
import Control.Applicative
import Data.Attoparsec.Text
import Data.Text
import Data.Proxy
import Format.Types
import GHC.TypeLits

instance DataFormat Text Char where
  decode = anyChar
  encode = singleton

instance DataFormat Text Int where
  decode = decimal
  encode = pack . show

instance (KnownSymbol s) => DecodeKindLit Text s where
  decodeKind p = string symbol *> return Proxy
    where symbol = pack (symbolVal p)

instance (KnownNat n) => DecodeKindLit Text n where
  decodeKind p = string nat *> return Proxy
    where nat = pack $ show $ natVal p

instance (DecodeKindLit Text s, KnownSymbol s) => DataFormat Text (Proxy s) where
  decode = decodeKind Proxy
  encode = pack . symbolVal

instance (DecodeKindLit Text s, KnownNat s) => DataFormat Text (Proxy s) where
  decode = decodeKind Proxy
  encode = pack . show . natVal

parseFormat :: DataFormat Text a => Parser a -> Text -> Either String a
parseFormat p = parseOnly (p <* endOfInput)
