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
import Data.HList
import Control.Isomorphism.Partial
import Control.Applicative (Alternative)

--------------------------------------------------------------------------------

-- The unit format. The parser succeeds without consuming any input
-- and does not print nothing at all.
unit :: Use Pure c m i => Format c m i '[]
unit = pure Nil

-- | 'between left right f' is a format in which f must occur between 
-- 'left' and 'right'
between :: SeqC Format Format c m i 
        => Format c m i '[] -> Format c m i '[] -> Format c m i xs -> Format c m i xs
between l r p = l *> p <* r

--failWith :: Reify f => f xs -> Format c m i xs
--failWith = Fail . toSList

-- Tries each format until one succeeds.
-- The given list may not be empty.
choice :: AltC Format Format c m i =>  [Format c m i xs] -> Format c m i xs
choice (x:xs) = P.foldr (<|>) (error "choice: Add Empty") (x:xs)
choice [] = error "Format c.Combinator.choice: empty list"

optional :: (AltC Format FMap c m i, Use Pure c m i) 
         => SFormat c m i a -> SFormat c m i (Maybe a)
optional f = (just <$> f) <|> (nothing <$> unit)

(<+>) :: (Alternative m, AltC Format FMap c m i)
      => SFormat c m i a -> SFormat c m i b -> SFormat c m i (Either a b)
f1 <+> f2 = (left <$> f1) <|> (right <$> f2)
