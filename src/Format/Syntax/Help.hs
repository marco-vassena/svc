{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE PolyKinds #-}

module Format.Syntax.Help where

import Data.TypeList.HList
import Format.Syntax.Base

-- | This piece of format syntax is used to provide some helpful feedback
-- message to the user in case of failure.
data Help c m i xs where
  Help :: (Reify (a m i), c m i a) => a m i xs -> String -> Help c m i xs

(<?>) :: (Use Help c m i,  
          Use    a c m i,
          Reify (a c m i)) 
      => a c m i xs -> String -> Format c m i xs
f <?> msg = format (Help f msg)

instance Reify (Help c m i) where
  toSList (Help f _) = toSList f
