{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}

module NetPbm where

import Prelude hiding ((>>=))
import Control.Isomorphism.Partial
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as B
import Data.HList
import Data.List
import Data.Word

import Format.Base
import Format.Combinator
import Format.Token
import Format.Parser
import Format.Parser.Generic
import Format.Parser.Attoparsec

import Data.Attoparsec.ByteString.Char8 (Parser)

-- TODO Move this to char module
int :: SFormat m Char Int
int = i <$> some digit
  where i :: Iso '[String] '[Int] 
        i = Iso f g (SCons SNil) (SCons SNil)
          where f :: HList '[ String ] -> Maybe (HList '[Int])
                f (Cons s _) = Just . hsingleton $ read s
                g :: HList '[ Int ] -> Maybe (HList '[String])
                g (Cons n _) = Just . hsingleton $ show n

-- TODO move to char module
spaces :: Format m Char '[]
spaces = some (char ' ' <|> char '\t' <|> char '\n')

data Pbm = Pbm Int Int [[Char]]
  deriving Show

pbm :: Iso '[Int, Int, [[Char]]] '[Pbm]
pbm = Iso (Just . hsingleton . happly Pbm) f (SCons (SCons (SCons SNil))) (SCons SNil)
  where f :: PFunction '[Pbm] '[Int, Int, [[Char]]]
        f (Cons (Pbm n m img) _) = Just $ Cons n (Cons m (Cons img Nil))

pbmFormat :: SFormat m Char Pbm
pbmFormat = pbm <$> pbmRawFormat

pbmRawFormat :: Format m Char '[Int, Int, [[Char]]]
pbmRawFormat = pbmHeader >>= \(Cons n (Cons m _)) -> img n m

pbmHeader :: Format m Char '[Int, Int]
pbmHeader = (string "P1\n" @> int <@ spaces) <@> int <@ spaces
        -- comment = char '#' @> many noneOf "\n" <@ char "\n"

img :: Int -> Int -> SFormat m Char [[Char]]
img n m = count n (count m (bit <@ spaces))
  where bit = oneOf "01"

pbmParser :: Parser (HList '[Pbm])
pbmParser = mkParser pbmFormat
