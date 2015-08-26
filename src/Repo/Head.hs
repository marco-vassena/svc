{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE GADTs #-}

module Repo.Head where

import Data.Hashable
import Data.DiffUtils hiding (Node)
import Repo.Path

-- | Abstract data type that tracks the diff of an object in a Path and 
-- maintain the latest version of the object
data Head a = Head {value :: a, path :: (Path a) }
  deriving Show

-- | Smart constructor that creates an Head out of a path.
mkHead :: (Hashable a, Diff a) => Path a -> Head a
mkHead r@(Root z) = Head z r
mkHead n@(Node p d e) = Head (patch e) n
mkHead m@(Merge p q d e) = Head (patch e) m

-- | Initialize a branch with the given object.
initBranch :: (Hashable a, Diff a) => a -> Head a
initBranch = mkHead . root

-- | Used to intuitively track the history of changes
-- Adds a new version
commit :: Diff a => a -> Head a -> Head a
commit n (Head o p) = Head n (node p d)
  where d = gdiff o n

-- | Merges two branches using the recursive three-way merge.
merge :: (Hashable a, Diff a) => Head a -> Head a -> Either [Conflict] (Head a)
merge (Head x p) (Head y q) = 
  case recursive3WayMerge p q of
    Left err -> Left err
    Right p -> Right $ mkHead p
    
-- | Merges the objects in the first two paths, using the object contained in the
-- common ancestor given as third argument.
mergeWithAncestor :: (Hashable a, Diff a) => Path a -> Path a -> Path a -> Either [Conflict] (Path a)
mergeWithAncestor p q a = 
  case diff3 x o y of
    Left err -> Left err
    Right e -> Right (mergePaths p q e)
  where x = currentValue p
        y = currentValue q
        o = currentValue a
 
-- Merges the object in two paths applying recursively the three-way merge.
recursive3WayMerge :: (Hashable a, Diff a) => Path a -> Path a -> Either [Conflict] (Path a)
recursive3WayMerge p q =
  case lca p q of
    One a -> mergeWithAncestor p q a
    Two a b -> 
      case recursive3WayMerge a b of
        Left err -> Left err
        Right c -> mergeWithAncestor p q c
