module Data.DiffUtils.Diff3 where

import Data.TypeList.DList
import Data.DiffUtils.Diff
import Data.DiffUtils.Diff3.Core

-- User friendly entry point
-- TODO: Provide user-friendly entry point, i.e. checks for expected type.
-- TODO maybe even more friendly expecting directly raw types instead of DList ?
-- TODO Safer interface: errors for types or conflicts.
diff3 :: DList f ys -> DList f xs -> DList f ys -> ES f xs ys
diff3 = undefined

