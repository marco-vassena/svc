{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}

-- This module provides common combinators

module Format.Combinator where

import Format.Base
import Control.Applicative
import Data.Functor.Identity
import Text.Parsec.Char
import Text.Parsec.Combinator
import Text.Parsec.Prim
import Format.HList

int :: (StringLike i, Stream i Identity Char) => Format i '[ Int ]
int = Target

sepBy :: Format i xs -> Format i ys -> Format i (Map [] xs)
sepBy p sep = undefined
