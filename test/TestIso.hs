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
        actual = case apply foldlTree $ Cons Leaf (Cons ts Nil) of
                  Nothing -> error "foldlTree failed"
                  Just (Cons t Nil) -> t

-- | Checks the correctness of foldlTree with the inverse semantics (unfoldl).
testFoldLUnapply :: Tree -> Bool
testFoldLUnapply t = actual == (expected t)
  where expected Leaf = [Leaf]
        expected (Branch t1 t2) = expected t1 ++ [ t2 ]
        actual = case unapply foldlTree $ Cons t Nil of
                    Nothing -> error "foldlTree failed"
                    Just (Cons t (Cons ts Nil)) -> t:ts 

--------------------------------------------------------------------------------

isSuccess :: Result -> Bool
isSuccess (Success _ _ _) = True
isSuccess _ = False

main :: IO ()
main = do
  r1 <- quickCheckResult testFoldLApply
  r2 <- quickCheckResult testFoldLUnapply
  if all isSuccess [r1, r2]
    then return ()
    else exitFailure
