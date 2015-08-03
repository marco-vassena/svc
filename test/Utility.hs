{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Utility where

import Data.TypeList.HList
import Control.Monad
import Test.QuickCheck
import Test.HUnit.Base

-- Auxiliray arbitrary instances
instance Arbitrary (HList '[]) where
  arbitrary = return Nil 

instance (Arbitrary x, Arbitrary (HList xs)) => Arbitrary (HList (x ': xs)) where
  arbitrary = liftM2 Cons arbitrary arbitrary

-- Throws an error if the printer fails
printWith :: Show a => (a -> Maybe b) -> a -> b
printWith f e = maybe (error msg) id (f e)
  where msg = "Printer failed on: " ++ show e

-- Throws an error if the parser fails
parseWith :: (String -> Maybe a) -> String -> a
parseWith f s = maybe (error msg) id (f s)
  where msg = "Parser failed on: " ++ s

hasFailed :: Counts -> Bool
hasFailed (Counts c t e f) = e > 0 || f > 0
