{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}

module Repo.Diff3 where

import GHC.Generics (Generic)
import Generics.Instant.TH
import qualified Generics.Instant.GDiff as G (diff)
import Generics.Instant.GDiff hiding (diff, Del, Ins, Cpy)
import Data.Typeable
import Data.Hashable

data Tree a = Node a [Tree a]
  deriving (Show, Eq, Typeable, Generic)

leaf :: a -> Tree a
leaf x = Node x []

class Metric a where
  -- Laws:
  --  d x y = d y x                  (symmetry)
  --  d x y >= 0                          (non-negativity)
  --  d x x = 0                           (identity)
  --  d x z <= d x y + d y z    (triangle inequality)
  distance :: a -> a -> Double

instance Metric Char where
  distance x y = if x == y then 0 else 1

instance Metric Int where
  distance x y = if x == y then 0 else 1

data ETree a = Ch2 Double a a (EList a)
             | Ins a (EList a)
             | Del a (EList a)
  deriving (Show, Eq)

data EList a = ConsA (ETree a) (EList a) -- Add
             | ConsD (ETree a) (EList a) -- Delete
             | ConsC (ETree a) (EList a) -- Change
             | Nil
  deriving (Show, Eq)

toList :: EList a -> [ETree a]
toList Nil = []
toList (ConsA t es) = t : toList es
toList (ConsC t es) = t : toList es
toList (ConsD t es) = t : toList es

-- At the moment we are not considering the size of the trees
cost :: ETree a -> Double
cost (Ch2 d _ _ es) = d + costs es
cost (Del _ es) = 1 + costs es
cost (Ins _ es) = 1 + costs es

-- TODO avoid list conversion ... use Foldable
costs :: EList a -> Double
costs = sum . map cost . toList

(&) :: ETree a -> ETree a -> ETree a
a & b = if cost a <= cost b then a else b

(&&&) :: EList a -> EList a -> EList a
as &&& bs = if costs as <= costs bs then as else bs

-- TODO memoization
diff :: Metric a => Tree a -> Tree a -> ETree a
diff n@(Node x xs) m@(Node y ys) = a & b & c
  where a = Del x (diffs xs [m])
        b = Ins y (diffs [n] ys) 
        c = Ch2 (distance x y) x y (diffs xs ys)

diffs :: Metric a => [Tree a] -> [Tree a] -> EList a 
diffs [] [] = Nil
diffs (x:xs) [] = ConsD (del x) (diffs xs [])
diffs [] (y:ys) = ConsA (ins y) (diffs [] ys)
diffs (x:xs) (y:ys) = a &&& b &&& c
  where a = ConsC (diff x y) (diffs xs ys)
        b = ConsD (del x) (diffs xs (y:ys))
        c = ConsA (ins y) (diffs (x:xs) ys)

ins, del :: Tree a -> ETree a
ins (Node x xs) = Ins x $ foldr ConsA Nil (map ins xs) 
del (Node x xs) = Del x $ foldr ConsD Nil (map del xs)

-- TODO 
-- diff3 (how ETrees are compared for conflicts?)
-- EList (ConsA / ConsD / ConsC)

-- Generic part
-- More interesting use case lists of lists of integers
-- > We need a more refined tree structure : nodes and leaves 
--   may contain arbitrary types and constructors
-- Issues:
--  > Subtrees with different types may be compared
--  > distance requires two elements of the same type (no existential)

-- The nice properties of the Tree view are
-- 1) Precise representation of embedding (shape change vs value change)
-- 2) It's easy to compare 2 edits to find conflicts.

-- In order to maintain the tree structure we cannot use simply Cpy, but 
-- we need Ch2 which encodes Cpy (when distance is 0) or a value change.
-- Without that we could not match properly examples like
-- 1          0
-- | \        | \
-- 2  3       2  3
-- Because we need to call diffs on the children.

-- Example with l1 l2 l3 : why is [1,4,5,2,3,6] a good resolution?
--  1) It preserves most of the ordering (embedding).
--  2) Values are not duplicated
--  3) Minimizes the changes to shape
--------------------------------------------------------------------------------
-- Example

t1, t2, t3 :: Tree Char

t1 = Node 'a' [Node 'b' [],
               Node 'c' [Node 'd' [],
                         Node 'e' []]]

t2 = Node 'a' [Node 'd' [Node 'b' []],
               Node 'e' []]

t3 = Node 'a' [Node 'b' [Node 'g' []],
               Node 'f' [Node 'd' [],
                         Node 'e' []]]

node :: a -> Tree a -> Tree a
node x t = Node x [t]

l1, l2, l3 :: Tree Int
l1 = foldr node (leaf 6) [1,2,3,4,5]
l2 = foldr node (leaf 6) [1,4,5,2,3]
l3 = foldr node (leaf 6) [1,2,4,5,3]

--------------------------------------------------------------------------------
-- GDiff for Tree

$(deriveAll ''Tree)
instance (Show a, GDiff a) => SEq      (Tree a) where shallowEq  = shallowEqDef
instance (Show a, GDiff a) => Build    (Tree a) where build      = buildDef
instance (Show a, GDiff a) => Children (Tree a) where children   = childrenDef
instance (Show a, GDiff a) => GDiff (Tree a)

instance Show a => Pretty (Tree a) where
  pretty (Node x _) = "Node " ++ show x

instance Hashable a => Hashable (Tree a) where

x = Node 'a' [leaf 'b', leaf 'c']
y = Node 'd' [leaf 'b', Node 'c' [leaf 'e']]
