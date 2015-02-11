{-# LANGUAGE GADTs #-}

module Repository where

import Data.Typeable
import Generics.Instant.TH
import Generics.Instant.GDiff

data Repo a where
  Repo :: GDiff a => [EditScript] -> Maybe a -> Repo a

-- The empty repository:
--  * empty history
--  * no value
empty :: GDiff a => Repo a
empty = Repo [] Nothing

-- Produces a new Repo containing the new value,
-- and keeps track in the history of the deltas
commit :: GDiff a => a -> Repo a -> Repo a
commit y (Repo hs x) = Repo (dF : hs) (Just y)
  where dF = diff x (Just y)

-- @back n r@ rolls back @n@ commits in the repo @r@
-- The returned repo is some kind of "detached state",
-- where the previous history is available, but 
-- the future commits are discarded.
back :: Int -> Repo a -> Repo a
back n (Repo hs v) = Repo past (foldr unsafePatch Nothing past)
  where (future, past) = splitAt n hs

-- Returns the n-th version of the repo.
-- (0-th is the empty repo).
version :: Int -> Repo a -> Repo a
version n r@(Repo hs _) = back (l - n) r
  where l = length hs

-- Calls patch and throws error if it fails
unsafePatch :: GDiff a => EditScript -> a -> a
unsafePatch d x = 
  case patch d x of
    Just y -> y
    Nothing -> error $ "patch:\t" ++ show d ++ "\nfailed over:\t" ++ show x

r0, r1, r2, r3 :: Repo Int
r0 = empty
r1 = commit 1 r0
r2 = commit 2 r1
r3 = commit 3 r2

-- Branching is the result of commiting from a previous state
-- b2 shares the first commits with r2, but the last differs.
b2 :: Repo Int
b2 = commit 4 r1

--------------------------------------------------------------------------------
-- Auxiliary GDiff instances
--------------------------------------------------------------------------------
-- TODO maybe move to library gdiff-ig

instance SEq (Maybe a) where
  shallowEq Nothing Nothing = True
  shallowEq (Just _) (Just _) = True
  shallowEq _ _ = False

instance GDiff a => Children (Maybe a) where
  children Nothing  = []
  children (Just x) = [Ex x]

instance Typeable a => Build (Maybe a)  where
  build Nothing l = Just (Nothing,l)
  build _ ((Ex x):r) = do y <- cast x
                          Just (Just y,r)
  build _ _ = Nothing

instance GDiff a => GDiff (Maybe a)

--------------------------------------------------------------------------------
-- Debugging

instance Show (Repo a) where
  show (Repo hs v) = unwords ["Repo", show hs, show v]
