{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}

module Format.Parser.Parsec where

import Control.Isomorphism.Partial
import Control.Applicative ((<$>), (<*>), pure)
import Data.HList
import Format.Base
import Format.Parser.Base
import Text.Parsec

-- TODO in principle you should only specify ParseToken
