{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}

-- | Definition of the help format combinator and its smart constructor.

module Format.Syntax.Help where

import Data.TypeList.HList
import Format.Syntax.Base

-- | Help Format descriptor.
-- It is used to provide error messages and feedback.
data Help c m i xs where
  Help :: (Reify (a m i), c m i a) => a m i xs -> String -> Help c m i xs

-- | Smart constructor
(<?>) :: (Use Format c m i, Use Help c m i) => Format c m i xs -> String -> Format c m i xs
f <?> msg = format (Help f msg)

instance Reify (Help c m i) where
  toSList (Help f _) = toSList f
