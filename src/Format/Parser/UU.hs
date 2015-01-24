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
import Format.Parser.GParser
import Text.ParserCombinators.UU.BasicInstances
import Text.ParserCombinators.UU.Core hiding (Fail)

instance (Bounded a, Ord a, Show a, IsLocationUpdatedBy loc a, ListLike state a) 
  => ParseToken (P (Str a state loc)) a where
  parseToken = pRange (minBound, maxBound)

instance (IsLocationUpdatedBy loc Char, ListLike state Char) 
  => ParseSatisfy (P (Str Char state loc)) Char where
  parseSatisfy p = pSatisfy p i
    where i = Insertion "Char" 'a' 5
