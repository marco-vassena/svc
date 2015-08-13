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

patch :: Diff b => ES '[ a ] '[ b ] -> b
patch = fromDTree . dHead . target 

unpatch :: Diff a => ES '[ a ] '[ b ] -> a
unpatch = fromDTree . dHead . source
