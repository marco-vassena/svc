{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}

-- This module defines some basic combinators, commonly found in parsing combinators libraries.

module Format.Combinator.Base where

import Prelude
import qualified Prelude as P
import Format.Syntax
import Data.TypeList.HList
import Control.Isomorphism.Partial
import Control.Applicative (Alternative)

-- | The unit format. The parser succeeds without consuming any input
-- and does not print nothing at all.
unit :: ApplicativeC c m i => Format c m i '[]
unit = pure Nil

-- | 'between left right f' corresponds to the format @f@ surrounded by 
-- the /trivial formats 'left' and 'right'.
between :: ApplicativeC c m i 
        => Format c m i '[] -> Format c m i '[] -> Format c m i xs -> Format c m i xs
between l r p = l *> p <* r

-- | It returns a format made by the alternative choice of all the formats in the list.
choice :: (AlternativeC c m i, KnownSList xs) =>  [Format c m i xs] -> Format c m i xs
choice xs = P.foldr (<|>) empty xs

-- | It marks the /optional/ presence of a format.
optional :: AlternativeC c m i
         => SFormat c m i a -> SFormat c m i (Maybe a)
optional f = (just <$> f) <|> (nothing <$> unit)

-- | Couples two alternatives in a @Either@ type.
(<+>) :: AlternativeC c m i
      => SFormat c m i a -> SFormat c m i b -> SFormat c m i (Either a b)
f1 <+> f2 = (left <$> f1) <|> (right <$> f2)
