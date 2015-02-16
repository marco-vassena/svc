{-# LANGUAGE GADTs #-}

module Repository where

import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as M
import Data.Typeable
import Generics.Instant.TH
import Generics.Instant.GDiff
import Control.Monad.Except
import Control.Monad.Trans.State.Lazy

-- Branch name
type BName = String

-- Reference to parents commits
type Parents a = [HashId]

-- An integer representing the Hash of the EditScript
-- used to uniquely identify commits.
type HashId = Int

-- Being Haskell a pure language we are not just 
-- making referencies to parents, but actually copies.
-- This may be inacceptable. Sharing must be preserved
-- ** especially ** when they are serialized.
data Commit a = Commit { hashId :: HashId,
                         delta :: EditScript,
                         parents :: Parents a}
  deriving Show

data Head a = Head { branch :: BName,
                     value  :: (Maybe a) }
  deriving Show

data RState a = RState { branches :: Map BName [Commit a],
                         tip :: (Head a) }

data RError = BranchNotFound String
  deriving Show

type Repo a b = StateT (RState a) (Except RError) b

runRepo :: Repo a b -> Either RError b
runRepo r = runExcept (evalStateT r initState)
  where initState = RState M.empty (Head "" Nothing)

-- Adds a branch with the given name
-- TODO fail if the branch is already present
newBranch :: BName -> Repo a ()
newBranch b = modify f
  where f (RState m h) = RState (M.insert b [] m) h

getBranch :: BName -> Repo a [Commit a]
getBranch b =  do
  m <- gets branches
  case M.lookup b m of
    Just cs -> return cs
    Nothing -> lift (throwError (BranchNotFound b))

getHead :: Repo a (Head a)
getHead = gets tip

putHead :: Head a -> Repo a ()
putHead h = modify f
  where f (RState m _) = RState m h

addCommit :: BName -> Commit a -> Repo a ()
addCommit b c = modify f
  where f (RState m h) = RState (M.adjust (c:) b m) h

setHead :: (Show a, GDiff a) => BName -> Repo a ()
setHead b = do
  cs <- getBranch b >>= \cs -> return [delta c | c <- cs]
  let v = foldr unsafePatch Nothing cs
  putHead (Head b v)

-- Change branch
switch :: (Show a, GDiff a) => BName -> Repo a ()
switch b = setHead b

getValue :: Repo a (Maybe a)
getValue = gets (value . tip)
  

-- Initialize repository:
--- * master branch
--  * empty history
--  * no value
initRepo :: (Show a, GDiff a) => Repo a ()
initRepo = do
  newBranch "master"
  setHead "master"

getParents b = do
  cs <- getBranch b
  case cs of
    [] -> return []
    (c:cs) -> return [hashId c]

-- Produces a new Repo containing the new value,
-- and keeps track in the history of the deltas
commit :: GDiff a => a -> Repo a ()
commit y = do
  Head b x <- getHead
  ps <- getParents b
  let d = diff x (Just y)
  let newCommit = Commit 0 d ps
  let newHead = Head b (Just y) 
  addCommit b newCommit
  putHead newHead
  
---- @back n r@ rolls back @n@ commits in the repo @r@
---- The returned repo is some kind of "detached state",
---- where the previous history is available, but 
---- the future commits are discarded.
----back :: Int -> Repo a -> Repo a
----back n (Repo hs v) = Repo past (foldr unsafePatch Nothing past)
----  where (future, past) = splitAt n hs
--
------ Returns the n-th version of the repo.
------ (0-th is the empty repo).
----version :: Int -> Repo a -> Repo a
----version n r@(Repo hs _) = back (l - n) r
----  where l = length hs

-- Calls patch and throws error if it fails
unsafePatch :: (GDiff a, Show a) => EditScript -> a -> a
unsafePatch d x = 
  case patch d x of
    Just y -> y
    Nothing -> error $ "patch:\t" ++ show d ++ "\nfailed over:\t" ++ show x


example0 :: Repo Int (Maybe Int)
example0 = do
  initRepo
  getValue

example1 :: Repo Int (Maybe Int)
example1 = do
  initRepo
  commit 1
  commit 2
  getValue

---- Branching is the result of commiting from a previous state
---- b2 shares the first commits with r2, but the last differs.
--b2 :: Repo Int
--b2 = commit 4 r1

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
