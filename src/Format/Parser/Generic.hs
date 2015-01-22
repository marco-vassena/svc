{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module Format.Parser.Generic where

import Control.Monad
import Control.Applicative
import Control.Isomorphism.Partial
import Data.HList
import Format.Base
import Format.Parser.Base

-- TODO write generic parser using applicative/monad interface
