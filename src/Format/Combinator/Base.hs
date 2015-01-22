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
import Format.Base
import Data.HList
import Control.Isomorphism.Partial

--------------------------------------------------------------------------------

-- The unit format. The parser succeeds without consuming any input
-- and does not print nothing at all.
unit :: Use Pure c m i '[] => Format c m i '[]
unit = pure Nil

-- | 'between left right f' is a format in which f must occur between 
-- 'left' and 'right'
between :: (Use Format c m i  xs,
            Use Format c m i '[],
            Use Seq    c m i  xs) 
        => Format c m i '[] -> Format c m i '[] -> Format c m i xs -> Format c m i xs
between l r p = l *> p <* r

--failWith :: Reify f => f xs -> Format c m i xs
--failWith = Fail . toSList

-- Tries each format until one succeeds.
-- The given list may not be empty.
choice :: (Use Alt    c m i xs, 
           Use Format c m i xs) => [Format c m i xs] -> Format c m i xs
choice (x:xs) = P.foldr (<|>) (error "choice: Add Empty") (x:xs)
choice [] = error "Format c.Combinator.choice: empty list"

optional :: (Use FMap   c m i '[Maybe a], 
             Use Alt c m i '[Maybe a],
             Use Format c m i '[Maybe a],
             Use Format c m i '[a],
             Use Pure   c m i '[],
             Use Format c m i '[]) => SFormat c m i a -> SFormat c m i (Maybe a)
optional f = (just <$> f) <|> (nothing <$> unit)

-- TODO : use type synonym to reduce (visually) the number of constraints
(<+>) :: (Use Alt    c m i '[Either a b],
          Use Format c m i '[Either a b],
          Use FMap   c m i '[Either a b],
          Use Format c m i '[a],
          Use Format c m i '[b]) 
      =>  SFormat c m i a -> SFormat c m i b -> SFormat c m i (Either a b)
f1 <+> f2 = (left <$> f1) <|> (right <$> f2)


--infixl 1 >>=
--(>>=) :: KnownSList ys => Format c m i xs -> (HList xs -> Format c m i ys) -> Format c m i (Append xs ys)
--(>>=) f k = Bind slist f k
