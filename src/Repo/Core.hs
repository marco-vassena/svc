{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-} -- For TypesOf
{-# LANGUAGE TypeOperators #-}

-- Module that defines the basic type facilites needed by Diff and Diff3.

module Repo.Core where

import Data.TypeList.DList
import Data.Type.Equality
import Data.Proxy

--------------------------------------------------------------------------------

-- Represents the fact that a type a belongs to a particular
-- family of mutually recursive data-types
class Metric f where
  -- Laws:
  --  d x y = d y x             (symmetry)
  --  d x y >= 0                (non-negativity)
  --  d x x = 0                 (identity)
  --  d x z <= d x y + d y z    (triangle inequality)
  distance :: f xs a -> f ys a -> Int

--------------------------------------------------------------------------------
