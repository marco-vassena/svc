-- | This test suite tests partial isomorphisms

{-# LANGUAGE GADTs #-}

module Main where

import Prelude
import qualified Prelude as P
import Control.Isomorphism.Partial
import Control.Monad
import Data.HList
import Data.List
import System.Exit
import Test.QuickCheck
import Tree

-- Generates arbitrary trees values
instance Arbitrary Tree where
  arbitrary = treeGen 10 
    where treeGen 0 = return Leaf
          treeGen n | n > 0 = oneof [return Leaf, liftM2 Branch subTree subTree]  
            where subTree = treeGen (n `div` 2) 

  shrink Leaf = []
  shrink (Branch t1 t2) = [t1, t2]

-- | Checks whether applying the foldlTree isomorphism is equivalent to
-- the plain equivalent foldl.
testFoldLApply :: [Tree] -> Bool
testFoldLApply ts = actual == expected
  where expected = P.foldl Branch Leaf ts
        actual = hHead $ apply foldlTree $ Cons Leaf (Cons ts Nil)

-- | Checks the correctness of foldlTree with the inverse semantics (unfoldl).
testFoldLUnapply :: Tree -> Bool
testFoldLUnapply t = actual == (expected t)
  where expected Leaf = []
        expected (Branch t1 t2) = expected t1 ++ [ t2 ]
        actual = case unapply foldlTree $ Cons t Nil of
                    Nothing -> error "foldlTree failed"
                    Just (Cons t (Cons ts Nil)) -> ts 

-- | Checks whether applying the foldrTree isomorphism is equivalent to
-- the plain equivalent foldr.
testFoldRApply :: [Tree] -> Bool
testFoldRApply ts = actual == expected
  where expected = P.foldr Branch Leaf ts
        actual = hHead . apply foldrTree $ Cons ts (Cons Leaf Nil) 

-- | Checks the correctness of foldrTree with the inverse semantics (unfoldr).
testFoldRUnapply :: Tree -> Bool
testFoldRUnapply t = actual == expected t
  where expected = unfoldr f
          where f Leaf = Nothing
                f (Branch t1 t2) = Just (t1, t2)
        actual = case unapply foldrTree $ Cons t Nil of
                    Nothing -> error "foldrTree failed"
                    Just (Cons ts (Cons t Nil)) -> ts

--------------------------------------------------------------------------------

isSuccess :: Result -> Bool
isSuccess (Success _ _ _) = True
isSuccess _ = False

main :: IO ()
main = do
  r1 <- quickCheckResult testFoldLApply
  r2 <- quickCheckResult testFoldLUnapply
  r3 <- quickCheckResult testFoldRApply
  r4 <- quickCheckResult testFoldRUnapply
  if all isSuccess [r1, r2, r3, r4]
    then return ()
    else exitFailure
