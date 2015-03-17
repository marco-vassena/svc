module Repo.Head where

import Generics.Instant.GDiff
import Repo.Path

-- Abstract data type that tracks the diff of an object in a Path and 
-- maintain the latest version of the object
data Head a = Head a (Path a)
  deriving Show

-- Smart constructor that creates an Head out of a path.
mkHead :: GDiff a => Path a -> Head a
mkHead r@(Root z) = Head z r
mkHead n@(Node p d e) = Head x n
  where x = patch' e (value (mkHead p))
mkHead m@(Merge p q d e) = mkHeadFromLca (lca p q) k
  where k h =  Head (patch' e (value h)) m

mkHeadFromLca :: GDiff a => Lca a -> (Head a -> Head a) -> Head a
mkHeadFromLca (One r)     k = k (mkHead r)
mkHeadFromLca (Two r0 r1) k = mkHeadFromLca (lca r0 r1) k

-- Calls error if patch fails.
patch' :: GDiff a => EditScript -> a -> a
patch' e x = 
  case patch e x of
    Just y -> y
    Nothing -> error "patch': patch failed"

value :: Head a -> a
value (Head x p) = x

path :: Head a -> Path a
path (Head x p) = p

-- Used to intuitively track the history of changes
-- Adds a new version
add :: GDiff a => a -> Head a -> Head a
add x (Head y p) = Head x (node p d)
  where d = diff y x

mergeHeads :: GDiff a => a -> Head a -> Head a -> Head a
mergeHeads x (Head _ p) (Head _ q) = Head x (mergeWith x p q)

-- Maybe this should be the default smart constructor for
-- merge rather than merge.
mergeWith :: GDiff a => a -> Path a -> Path a -> Path a
mergeWith x p1 p2 = merge p1 p2 (diff v x)
  where v = value h 
        h = mkHeadFromLca (lca p1 p2) id
