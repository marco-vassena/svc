-- | This test suite tests partial isomorphisms

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Main where

import Prelude
import qualified Prelude as P
import Control.Isomorphism.Partial
import Control.Monad
import Data.HList
import Data.Maybe
import Data.Tuple
import qualified Data.List as L
import System.Exit
import Test.QuickCheck
import Test.QuickCheck.Test
import Tree
import Utility

-- @foldlTree@ and @foldrTree@ are shorthands for respecitvely @foldl branch@ and @foldr branch@
-- TODO maybe use explicitly foldl branch / foldr branch in order to show how they are equivalent

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
        actual = hHead . apply foldlTree $ Cons Leaf (Cons ts Nil)

-- | Checks the correctness of foldlTree with the inverse semantics (unfoldl).
-- unfoldl can be expressed as unfoldr reversing the final list and switching the arugments
-- of the generator function (unapply branch).
testFoldLUnapply :: HList '[Tree] -> Bool
testFoldLUnapply hs = actual == expected
  where expected = hsingleton $ reverse (L.unfoldr f hs)
        f :: HList '[Tree] -> Maybe (Tree, HList '[Tree])
        f x = unapply branch x >>= \ (Cons t1 (Cons t2 Nil)) -> return (t2, Cons t1 Nil)
        actual = hTail . fromJust $ unapply foldlTree hs 

-- | Checks whether applying the foldrTree isomorphism is equivalent to
-- the plain equivalent foldr.
-- The constructor Branch is equivalent to apply branch, up to HList packing.
testFoldRApply :: HList '[[Tree]] -> Bool
testFoldRApply hs@(Cons ts Nil) = actual == expected
  where expected = P.foldr Branch Leaf ts
        actual = hHead . apply foldrTree $ Cons Leaf hs

-- | Checks the correctness of foldrTree with the inverse semantics (unfoldr).
testFoldRUnapply :: HList '[Tree] -> Bool
testFoldRUnapply hs = actual == expected
  where expected = hsingleton $ L.unfoldr f hs
        f :: HList '[Tree] -> Maybe (Tree, HList '[Tree])
        f x = unapply branch x >>= \ (Cons t1 hs) -> return (t1, hs)
        actual = hTail . fromJust $ unapply foldrTree hs

-- It holds:
--
-- > unfoldr f' (foldr f z xs) == xs
--
-- when 
--
-- > f' (f x y) = Just (x,y)
-- > f' z       = Nothing
--
-- Here @f@ is @apply branch@ and @f'@ is @unapply branch@
-- The conditions are satisfied when @z@ is @Leaf@.
--
testFoldRRightInverse :: [Tree] -> Bool
testFoldRRightInverse ts = actual == expected
  where expected = Cons Leaf (Cons ts Nil)
        folded = apply foldrTree (Cons Leaf (Cons ts Nil))
        actual = fromJust . unapply foldrTree $ folded

testFoldRLeftInverse :: Tree -> Bool
testFoldRLeftInverse t = actual == expected
  where expected = Cons t Nil
        unfolded = fromJust $ unapply foldrTree (hsingleton t)
        actual = apply foldrTree unfolded

testFoldLRightInverse :: [Tree] -> Bool
testFoldLRightInverse ts = actual == expected
  where expected = Cons Leaf (Cons ts Nil)
        folded = apply foldlTree (Cons Leaf (Cons ts Nil))
        actual = fromJust . unapply foldlTree $ folded

testFoldLLeftInverse :: Tree -> Bool
testFoldLLeftInverse t = actual == expected
  where expected = Cons t Nil
        unfolded = fromJust $ unapply foldlTree (hsingleton t)
        actual = apply foldlTree unfolded

main :: IO ()
main = do
  r1 <- quickCheckResult testFoldLApply
  r2 <- quickCheckResult testFoldLUnapply
  r3 <- quickCheckResult testFoldRApply
  r4 <- quickCheckResult testFoldRUnapply
  r5 <- quickCheckResult testFoldRRightInverse
  r6 <- quickCheckResult testFoldRLeftInverse 
  r7 <- quickCheckResult testFoldLRightInverse 
  r8 <- quickCheckResult testFoldLLeftInverse 
  if all isSuccess [r1,r2,r3,r4,r5,r6,r7,r8]
    then return ()
    else exitFailure
