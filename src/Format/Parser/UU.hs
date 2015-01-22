{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Format.Parser.UU where

import Control.Isomorphism.Partial
import Data.ListLike
import Data.HList
import Format.Base
import Format.Parser
import Text.ParserCombinators.UU.BasicInstances
import Text.ParserCombinators.UU.Core hiding (Fail)

-- TODO in principle you should only specify ParseToken
