{-# LANGUAGE DeriveGeneric #-}

module Repo.Path where

import GHC.Generics (Generic)
import Generics.Instant.GDiff
import Data.Hashable
import Data.List
import qualified Data.Set as S
import Data.Set (Set)

-- A positive number that represents the length of a path from the Root.
type Depth = Int

-- Kept abstract to enforce the invariants
data  Path a = Root a
             | Node  (Path a) !Depth EditScript
             | Merge (Path a) (Path a) !Depth EditScript
  deriving (Show, Generic)

instance Hashable a => Hashable (Path a) where

-- Returns the depth of a path
depth :: Path a -> Depth
depth (Root _) = 0
depth (Node _ d _) = d
depth (Merge _ _ d _) = d

-- Smart constructors, which maintain the invariant about depth.
root :: a ->  Path a
root = Root

node ::  Path a -> EditScript ->  Path a
node p = Node p (depth p + 1)

-- Merges The path with the lowest hash is always put to the left.
merge :: Hashable a => Path a ->  Path a -> EditScript ->  Path a
merge p1 p2 e | hash p1 < hash p2 = Merge p1 p2 (max (depth p1) (depth p2) + 1) e
merge p1 p2 e | otherwise         = merge p2 p1 e

--------------------------------------------------------------------------------

-- Wrapper of Path used to overload Hash-based operations.
newtype HPath a = HPath {dpath :: Path a}

-- Ord and Eq instance use the hash of the  Path a
instance Hashable a => Eq (HPath a) where
  HPath p == HPath q = hash p == hash q

instance Hashable a => Ord (HPath a) where
  HPath p <= HPath q = hash p <= hash q

-- Returns all the subpaths of a path, grouped by depth level, in descending order.
levels :: Hashable a => Path a -> [(Depth, Set (HPath a))]
levels r@(Root x)= [(depth r, S.singleton (HPath r))]
levels n@(Node p d _) = (d, S.singleton (HPath n)) : levels p
levels m@(Merge p1 p2 d _) = (d, S.singleton (HPath m)) : combine (levels p1) (levels p2)

combine :: Hashable a => [(Depth, Set (HPath a))] -> [(Depth, Set (HPath a))] -> [(Depth, Set (HPath a))] 
combine [] ds = ds
combine ds [] = ds
combine a@((d1,xs):ds1) b@((d2,ys):ds2) = 
  case compare d1 d2 of
    LT -> (d2, ys) : combine a ds2
    EQ -> (d1, xs `S.union` ys) : combine ds1 ds2
    GT -> (d1, xs) : combine ds1 b

--------------------------------------------------------------------------------

data Lca a = One (Path a)
           | Two (Path a) (Path a)
  deriving Show

-- Computes the lowest common ancestor of two paths.
lca :: Hashable a => Path a ->  Path a -> Lca a
lca p1 p2 = 
  case find (not . S.null) (zipWith common ls1 ls2) of
    Just s -> 
      case S.toList s of
        [ r ] -> One (dpath r)
        [r0, r1] -> Two (dpath r0) (dpath r1)
        _ -> error "lca: More than 2 common ancestors found"
    Nothing -> error "lca: No common ancestor found"
  where d = min (depth p1) (depth p2)
        ls1 = dropWhile ((> d) . fst) (levels p1)
        ls2 = dropWhile ((> d) . fst) (levels p2)
        common (_, ls1) (_, ls2) = S.intersection ls1 ls2
