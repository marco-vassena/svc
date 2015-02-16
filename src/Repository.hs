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
type Parents a = [Commit a] -- TODO HashId should probably be enough

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

getCurrentBranch :: Repo a [Commit a]
getCurrentBranch = gets (branch . tip) >>= getBranch

getBranch :: BName -> Repo a [Commit a]
getBranch b =  do
  m <- gets branches
  case M.lookup b m of
    Just cs -> return cs
    Nothing -> lift (throwError (BranchNotFound b))

getHead :: Repo a (Head a)
getHead = gets tip

putHead :: Head a -> Repo a ()
putHead h = modifyHead (const h)
  where f (RState m _) = RState m h

modifyHead :: (Head a -> Head a) -> Repo a ()
modifyHead f = modify g
  where g (RState m h) = RState m (f h)

putValue :: Maybe a -> Repo a ()
putValue v = modifyHead g
  where g (Head b _) = Head b v

addCommit :: BName -> Commit a -> Repo a ()
addCommit b c = modify f
  where f (RState m h) = RState (M.adjust (c:) b m) h

setHead :: (Show a, GDiff a) => BName -> Repo a ()
setHead b = do
  v <- getBranch b >>= return . computeValue
  putHead (Head b v)

computeValue :: (Show a, GDiff a) => [Commit a] -> Maybe a
computeValue cs = foldr unsafePatch Nothing ds
  where ds = [delta c | c <- cs]

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
    (c:cs) -> return [c]

-- Produces a new Repo containing the new value,
-- and keeps track in the history of the deltas
commit :: GDiff a => a -> Repo a ()
commit y = do
  Head b x <- getHead
  ps <- getParents b
  let d = diff x (Just y)
  let newCommit = Commit 0 d ps
  addCommit b newCommit
  putValue (Just y)
  
-- @back n r@ rolls back @n@ commits in the repo @r@
-- The returned repo is some kind of "detached state",
-- where the previous history is available, but 
-- the future commits are discarded.
back :: (Show a, GDiff a) => Int -> Repo a ()
back n = do
  cs <- getCurrentBranch 
  let (future, past) = splitAt n cs
  let v = computeValue past
  putValue v

-- Returns the n-th version of the repo.
-- (0-th is the empty repo).
version :: (Show a, GDiff a) => Int -> Repo a ()
version n = do
  l <- getCurrentBranch >>= return . length 
  back (l - n)

-- Calls patch and throws error if it fails
unsafePatch :: (GDiff a, Show a) => EditScript -> a -> a
unsafePatch d x = 
  case patch d x of
    Just y -> y
    Nothing -> error $ "patch:\t" ++ show d ++ "\nfailed over:\t" ++ show x

-- TODO use set, they may not be unique
commonAncestors :: Commit a -> Commit a -> [Commit a]
commonAncestors c1 c2 = 
  let cs = concat [commonAncestors p1 p2 | p1 <- parents c1, p2 <- parents c2] in
  if hashId c1 == hashId c2 
    then c1 : cs
    else cs

merge :: BName -> Repo Int ()
merge b = do
  c1 <- getCurrentBranch >>= return . head
  c2 <- getBranch b >>= return . head
  case commonAncestors c1 c2 of
    [] -> error $ "No common ancestor with " ++ b 
    [ p ] -> error "3-way-merge"
    _ -> error "octupus merge"

--------------------------------------------------------------------------------
-- Examples

base :: Repo Int ()
base = initRepo

c1 :: Repo Int ()
c1 = base >> commit 1

c23 :: Repo Int ()
c23 = commit 2 >> commit 3

back2 :: Repo Int ()
back2 = c23 >> back 2

branchDev :: Repo Int ()
branchDev = newBranch "dev" 

d4 :: Repo Int ()
d4 = branchDev >> commit 4

mergeOk :: Repo Int ()
mergeOk = do
  c1
  (newBranch "dev" >> setHead "dev" >> commit 4)
  setHead "master"
  c23
  merge "dev"

conflict :: Repo Int ()
conflict = do
  c1 
  (newBranch "dev" >> setHead "dev" >> commit 4)
  setHead "master" 
  c23 
  merge "dev"
  
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
-- Debug

showRepo :: (GDiff a, Show a) => Repo a b -> String
showRepo r = 
  case runRepo (r >> showInternal) of
    Left e -> show e
    Right s -> s
  where showInternal :: (GDiff a, Show a) => Repo a String
        showInternal = do
          bs <- gets branches >>= return . M.assocs
          let bs' = [(b, cs, (scanr (\c -> unsafePatch (delta c)) Nothing cs)) | (b, cs) <- bs]
          return . concatMap unlines $ [ b : zipWith showCommit cs vs | (b , cs, vs) <- bs']

        showCommit :: Show a => Commit a -> Maybe a -> String
        showCommit c a = unwords ["\t", show (hashId c), show a]
