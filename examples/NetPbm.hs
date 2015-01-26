{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}

module NetPbm where

import Prelude hiding ((>>=))
import Control.Isomorphism.Partial
import qualified Control.Applicative as A
import qualified Control.Monad as M
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as B
import Data.HList
import Data.List
import Data.Word

import Format.Base hiding (fail)
import Format.Combinator
import Format.Token
import Format.Parser
import Format.Parser.GParser
import Format.Parser.Parsec
import Format.Printer.Naive

import Text.Parsec (Parsec, eof, parse)

import Util

-- TODO move to char module
spaces :: (Use Satisfy  c m Char, 
           AlternativeC c m Char) 
       => Format c m Char '[]
spaces = some (char ' ' <|> char '\t' <|> char '\n')

data Pbm = Pbm Int Int [[Char]]
  deriving Show

pbm :: Iso '[Int, Int, [[Char]]] '[Pbm]
pbm = Iso (Just . hsingleton . happly Pbm) f (SCons (SCons (SCons SNil))) (SCons SNil)
  where f :: PFunction '[Pbm] '[Int, Int, [[Char]]]
        f (Cons (Pbm n m img) _) = Just $ Cons n (Cons m (Cons img Nil))

pbmFormat :: (Use Bind     c m Char, 
              Use Satisfy  c m Char, 
              AlternativeC c m Char) 
          => SFormat c m Char Pbm
pbmFormat = pbm <$> pbmRawFormat

pbmRawFormat :: (Use Bind     c m Char, 
                 Use Satisfy  c m Char, 
                 AlternativeC c m Char) 
             => Format c m Char '[Int, Int, [[Char]]]
pbmRawFormat = pbmHeader >>= \(Cons n (Cons m _)) -> img n m

pbmHeader :: (AlternativeC c m Char, 
              Use Satisfy c m Char) 
          => Format c m Char '[Int, Int]
pbmHeader = (string "P1\n" *> comment *> int <* spaces) <*> int <* spaces 
  
comment :: (AlternativeC c m Char, 
            Use Satisfy c m Char) 
        => Format c m Char '[]
comment = ignore (hsingleton Nothing) <$> optional cm
  where cm = char '#' *> manyTill (satisfy (/= '\n')) (char '\n')

img :: (Use Satisfy c m Char, AlternativeC c m Char) 
    => Int -> Int -> SFormat c m Char [[Char]]
img n m = count n (count m (bit <* spaces))
  where bit = oneOf "01"

pbmParser :: Parsec ByteString () Pbm
pbmParser = hHead A.<$> (mkParser pbmFormat) A.<* eof

pbmPrinter :: Pbm -> Maybe ByteString
pbmPrinter = mkPrinter pbmFormat . hsingleton

roundtrip :: ByteString -> IO ByteString
roundtrip s = do 
  case parse pbmParser "" s of
    Left e -> fail (show e) 
    Right p -> print p >> maybe (fail "Printer Failed") return (pbmPrinter p)

test :: String -> IO ()
test s = B.readFile s M.>>= roundtrip M.>>= B.putStrLn

main :: IO ()
main = M.forever $ getLine M.>>= test
