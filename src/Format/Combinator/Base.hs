{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}

module Format.Combinator.Base where

import Prelude
import qualified Prelude as P
import Format.Syntax
import Data.TypeList.HList
import Control.Isomorphism.Partial
import Control.Applicative (Alternative)

--------------------------------------------------------------------------------

-- The unit format. The parser succeeds without consuming any input
-- and does not print nothing at all.
unit :: ApplicativeC c m i => Format c m i '[]
unit = pure Nil

-- | 'between left right f' is a format in which f must occur between 
-- 'left' and 'right'
between :: ApplicativeC c m i 
        => Format c m i '[] -> Format c m i '[] -> Format c m i xs -> Format c m i xs
between l r p = l *> p <* r

--failWith :: Reify f => f xs -> Format c m i xs
--failWith = Fail . toSList

-- Tries each format until one succeeds.
choice :: (AlternativeC c m i, KnownSList xs) =>  [Format c m i xs] -> Format c m i xs
choice xs = P.foldr (<|>) empty xs

optional :: AlternativeC c m i
         => SFormat c m i a -> SFormat c m i (Maybe a)
optional f = (just <$> f) <|> (nothing <$> unit)

(<+>) :: AlternativeC c m i
      => SFormat c m i a -> SFormat c m i b -> SFormat c m i (Either a b)
f1 <+> f2 = (left <$> f1) <|> (right <$> f2)
