-- This module provides common combinators

module Format.Combinator (
    module Format.Combinator.Base
  , many
  , some
  , sepBy
  ) where

import Format.Combinator.Base
import qualified Format.Combinator.Prim as P
import Data.HList
import Format.Base

many :: KnownSList xs => Format m i xs -> Format m i (Map [] xs)
many = P.many slist

some :: KnownSList xs => Format m i xs -> Format m i (Map [] xs)
some = P.some slist

sepBy :: KnownSList xs => Format m i xs -> Format m i '[] -> Format m i (Map [] xs)
sepBy = P.sepBy slist
