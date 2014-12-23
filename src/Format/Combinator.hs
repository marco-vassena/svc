-- This module provides common combinators

module Format.Combinator (
    module Format.Combinator.Base
  , many
  ) where

import Format.Combinator.Base
import qualified Format.Combinator.Prim as P
import Data.HList
import Format.Base

many :: KnownSList xs => Format m i xs -> Format m i (Map [] xs)
many = P.many slist
