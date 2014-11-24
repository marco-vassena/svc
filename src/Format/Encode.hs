{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Format.Encode where

import Text.Parsec.ByteString ()
import Text.Parsec.Text ()
import Data.ByteString (ByteString)
import qualified Data.ByteString as W (singleton)
import qualified Data.ByteString.Char8 as B
import Data.Foldable
import Data.Monoid
import Data.Proxy
import Data.Text (Text)
import qualified Data.Text as T
import Data.Word
import GHC.TypeLits
import Format.Base

class Encode i a where
  gencode :: a -> i

instance (Monoid i, Encode i a, Encode i b) => Encode i (a :*: b) where
  gencode (a :*: b) = gencode a <> gencode b

instance (Monoid i, Encode i a, Encode i b) => Encode i (a :<*: b) where
  gencode (a :<*: b) = gencode a <> gencode b

instance (Monoid i, Encode i a, Encode i b) => Encode i (a :*>: b) where
  gencode (a :*>: b) = gencode a <> gencode b

instance (Monoid i, Encode i a, Encode i b) => Encode i (a :+: b) where
  gencode (L a) = gencode a
  gencode (R b) = gencode b

instance (Monoid i, Encode i a, Encode i b) => Encode i (a :~>: b) where
  gencode (a :~>: b) = gencode a <> gencode b

instance (Monoid i, Encode i a) => Encode i (Many a) where
  gencode (Many as) = mconcat (fmap gencode as)

instance (Monoid i, Encode i a) => Encode i (Some a) where
  gencode (Some a as) = mconcat (fmap gencode (a : as))

-- Optional presence
instance (Monoid i, Encode i a) => Encode i (Maybe a) where
  gencode (Just a) = gencode a
  gencode Nothing = mempty

-- This instance triggers overlapping instances due to the open-world assumption.
-- What is the best way to deal with this?
--instance (Monoid i, Foldable t, Encode i a) => Encode i (t a) where
--  gencode = foldMap gencode

--------------------------------------------------------------------------------
-- ByteString instances

instance Encode ByteString Char where
  gencode = B.singleton

instance Encode ByteString Int where
  gencode = B.pack . show

instance Encode ByteString Word8 where
  gencode = W.singleton

instance (KnownSymbol s) => Encode ByteString (Proxy s) where
  gencode = B.pack . symbolVal

instance (KnownNat n) => Encode ByteString (Proxy n) where
  gencode = B.pack . show . natVal 

instance Encode ByteString (NoneOf s) where
  gencode (NoneOf _ s) = B.singleton s

--------------------------------------------------------------------------------
-- Text instances 

instance Encode Text Char where
  gencode = T.singleton

instance Encode Text Int where
  gencode = T.pack . show

instance (KnownSymbol s) => Encode Text (Proxy s) where
  gencode = T.pack . symbolVal

instance (KnownNat n) => Encode Text (Proxy n) where
  gencode = T.pack . show . natVal

instance Encode Text (NoneOf s) where
  gencode (NoneOf _ s) = T.singleton s
