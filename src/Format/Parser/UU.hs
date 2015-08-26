{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

-- This module contains the hook instances for uu-parsinglib

module Format.Parser.UU where

import Control.Isomorphism.Partial
import Data.ListLike
import Data.TypeList.HList
import Format.Parser
import Format.Parser.GParser
import Text.ParserCombinators.UU.BasicInstances
import Text.ParserCombinators.UU.Core hiding (Fail)

instance (IsLocationUpdatedBy loc Char, ListLike state Char) 
  => ParseSatisfy (P (Str Char state loc)) Char where
  parseSatisfy p = pSatisfy p i
    where i = Insertion "Char" 'a' 5

instance ParseHelp (P (Str a state loc)) where
  parseHelp = (<?>)
