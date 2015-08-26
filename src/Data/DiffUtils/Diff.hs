{-# LANGUAGE DataKinds #-}

module Data.DiffUtils.Diff (
    module Data.DiffUtils.Diff.Core
  , module Data.DiffUtils.Diff.DList 
  , module Data.TypeList.TList
  , patch
  , unpatch )where

import Data.TypeList.TList
import Data.DiffUtils.Diff.Core
import Data.DiffUtils.Diff.DList

-- Retrieves the raw target object of a singleton-edit script.
patch :: Diff b => ES xs '[ b ] -> b
patch = fromDTree . dHead . target 

-- Retrieves the raw source object of a singleton-typed edit script.
unpatch :: Diff a => ES '[ a ] ys -> a
unpatch = fromDTree . dHead . source
