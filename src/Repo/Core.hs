{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-} -- For TypesOf
{-# LANGUAGE TypeOperators #-}

-- Module that defines the basic type facilites needed by Diff and Diff3.
-- TODO probably just remove this module

module Repo.Core where

import Data.TypeList.DList
import Data.Type.Equality
import Data.Proxy

--------------------------------------------------------------------------------
