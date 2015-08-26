{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}

module Format.Parser.Base where

import Format.Syntax
import Data.TypeList.HList

-- | The class @ParseWith m i a@ represents the parsing semantics:
-- 
-- * @m@ is the parser data type
-- * @i@ is the token type
-- * @a@ is the format descriptor whose parsing semantics is given
--
class ParseWith (m :: * -> *) (i :: *) a where
  mkParser' :: a m i xs -> m (HList xs)
 
-- | Entry point to be used instead of @mkParser'@.
-- It fixes the constraint type variable, thus avoiding ambiguities.
mkParser :: Use a ParseWith m i => a ParseWith m i xs -> m (HList xs)
mkParser = mkParser'
