-- Utility functions to print and parse with formats

{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Format.Prim where

import Format.Base
import Format.Parser
import Format.Printer
import Data.HList
import Data.Monoid
import Data.Functor.Identity
import qualified Text.Parsec as P
import Text.Parsec hiding (Parsec, parseTest)
import Text.Parsec.Char
import Control.Applicative

-- TODO move specific implementation to specific library modules

type Parsec s = P.ParsecT s () Identity 

instance Stream s Identity Char => ParseToken (ParsecT s () Identity) Char where
  parseToken = anyChar


type instance StreamOf Char = String

instance PrintToken (Either String) Char where
  printToken = return . (:[])

--------------------------------------------------------------------------------
-- Mainly used for testing

parseTest :: (Stream s Identity Char) => Format (Parsec s) Char xs -> s -> IO (HList xs)
parseTest f input = either (fail . show) return (P.parse (p <* P.eof) "" input)
  where p = mkParser f
   
printTest :: Format (Either String) Char xs -> HList xs -> IO ()
printTest f a = either (fail . show) print (p a)
  where p = mkPrinter f


-- It looks difficult to compose two different semantics in the same function.
-- m is unique, thus either a wrapper type that encodes both is needed.
-- Parse something and prints it right away using the given format.
--roundTrip :: Format (Parsec s) Char a -> s -> IO ()
--roundTrip f input = do
--  res <- parseTest f input 
--  printTest f res
