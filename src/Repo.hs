module Repo (
    Depth
  , Path
  , depth

  , Lca
  , lca

  , Head
  , mkHead
  , value
  , path
  , add
  , mergeHeads 
 
  ) where

import Repo.Path
import Repo.Head

-- TODO move Diff3 and Diff to separate modules

