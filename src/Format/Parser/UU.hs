{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Format.Parser.UU where

import Format.Parser
import Text.ParserCombinators.UU.BasicInstances
import Text.ParserCombinators.UU.Core
import Data.ListLike
 
instance  (IsLocationUpdatedBy loc Char, ListLike state Char) 
  => ParseToken (P (Str Char state loc)) Char where
  
  parseToken = pRange (minBound, maxBound)
